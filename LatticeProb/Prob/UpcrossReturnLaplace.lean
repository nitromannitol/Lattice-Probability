import Mathlib
import LatticeProb.Prob.UpcrossRenewalReturn
import LatticeProb.Prob.UpcrossReturn
import LatticeProb.Prob.ExpNegLtOne

/-!
# The Laplace transform of the return time after a down-crossing is below `1`

For `q > 0`, `c > 0` and a probability measure `ν` on `C(ℝ≥0, ℝ)` carried by paths started at `0`,
the integral `∫ e^{-q (return time)} dν` is strictly below `1`, because the return time
`upcrossReturn c v ≥ hitFrom (-c) 0 v` is strictly positive for every continuous path started at `0`.
It is applied to the law of the Brownian path with drift.

* `LatticeProb.lintegral_expNeg_upcrossReturn_lt_one`: general `ν`;
* `LatticeProb.lintegral_expNeg_upcrossReturn_lt_one_brownian`: `ν` the law of Brownian motion with
  drift.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- For a probability measure `ν` on paths carried by paths started at `0`, the Laplace transform of
the return time after the first down-crossing of `-c` is below `1`. -/
theorem lintegral_expNeg_upcrossReturn_lt_one {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (h0 : ∀ᵐ v ∂ν, v 0 = 0) {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 0 < q) :
    ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ)) ∂ν < 1 := by
  have hpos : ∀ v : C(ℝ≥0, ℝ), v 0 = 0 → 0 < upcrossReturn c (v : ℝ≥0 → ℝ) := fun v hv =>
    lt_of_lt_of_le (zero_lt_hitFrom_neg v.continuous hv hc) (hitFrom_neg_le_upcrossReturn c _)
  have hfi : ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ)) ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ : C(ℝ≥0, ℝ), 1 ∂ν) (by simp) ?_
    exact lintegral_mono fun v => expNeg_le_one hq.le _
  have hlt := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt (μ := ν)
    (g := fun _ => (1 : ℝ≥0∞)) measurable_const.aemeasurable hfi
    (Filter.Eventually.of_forall fun v => expNeg_le_one hq.le _)
    (h0.mono fun v hv => (expNeg_lt_one hq (hpos v hv)).ne).frequently
  simpa using hlt

/-- The Laplace transform of the return time after the first down-crossing of `-c`, under the law of
the Brownian path with drift, is below `1`. -/
theorem lintegral_expNeg_upcrossReturn_lt_one_brownian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 0 < q) :
    ∫⁻ v : C(ℝ≥0, ℝ), expNeg q (upcrossReturn c (v : ℝ≥0 → ℝ))
      ∂((P.map (pathMap B hcont)).map (driftMap mu)) < 1 := by
  have hpm : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
  have : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    (Measure.isProbabilityMeasure_map_iff hpm.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((P.map (pathMap B hcont)).map (driftMap mu)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_driftMap mu).aemeasurable).2 inferInstance
  refine lintegral_expNeg_upcrossReturn_lt_one ?_ hc hq
  have hev : Measurable fun v : C(ℝ≥0, ℝ) => v 0 :=
    (ContinuousMapBorel.ContinuousMap.measurable_iff_eval.1 measurable_id) 0
  have hset : MeasurableSet {v : C(ℝ≥0, ℝ) | v 0 = 0} := measurableSet_eq_fun hev measurable_const
  have h1 : ∀ᵐ x ∂(P.map (pathMap B hcont)), driftMap mu x ∈ {v : C(ℝ≥0, ℝ) | v 0 = 0} := by
    rw [ae_map_iff hpm.aemeasurable (hset.preimage (measurable_driftMap mu))]
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    simp [driftMap, pathMap, hω]
  exact (ae_map_iff (measurable_driftMap mu).aemeasurable hset).2 h1

end LatticeProb
