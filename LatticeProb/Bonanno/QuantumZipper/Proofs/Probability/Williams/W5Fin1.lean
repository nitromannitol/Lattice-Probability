/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Fin1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Main3

/-!
# W5 (part 9): the hitting time of `-c` by the down-drift process has finite mean

Preparation for W5(ii) (de-integration) of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1): the killed
time integrals of W5(i) are finite for bounded `g`, because `E[T_c] < ∞` for
`T_c = hitLevel X (-c)`, `X = dpath σ (-μ) b` (`lintegral_hitLevel_lt_top`).

Proof: layer-cake formula `E T = ∫_0^∞ P(T > m) dm` (mathlib `lintegral_eq_lintegral_meas_lt`),
`{T > m} ⊆ {X_m ≥ -c}`, and the Chernoff bound (mathlib `measure_ge_le_exp_mul_mgf`) with the
Gaussian moment generating function at `t = μ/σ²`:
`P(X_m ≥ -c) ≤ exp(μc/σ²) exp(-μ² m/(2σ²))`. Standard; own assembly.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- Chernoff bound for the down-drift process. -/
theorem measure_dpath_ge_le (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) (c : ℝ) {m : ℝ}
    (hm : 0 < m) :
    P {ω | -c ≤ dpath σ (-μ) b ω m.toNNReal}
      ≤ ENNReal.ofReal (Real.exp (μ * c / σ ^ 2) * Real.exp (-(μ ^ 2 / (2 * σ ^ 2)) * m)) := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hX := hasLaw_dpath hb σ (-μ) hm
  have hmap := Measure.map_apply_of_aemeasurable hX.aemeasurable (s := {y : ℝ | -c ≤ y})
    (measurableSet_le measurable_const measurable_id)
  rw [hX.map_eq] at hmap
  have ht0 : 0 ≤ μ / σ ^ 2 := by positivity
  have hch := measure_ge_le_exp_mul_mgf (μ := gaussianReal (-μ * m) (occVar σ m))
    (X := fun x => x) (-c) ht0 (integrable_exp_mul_gaussianReal (μ / σ ^ 2))
  rw [mgf_fun_id_gaussianReal, coe_occVar σ hm.le] at hch
  calc P {ω | -c ≤ dpath σ (-μ) b ω m.toNNReal}
      = ENNReal.ofReal ((gaussianReal (-μ * m) (occVar σ m)).real {y : ℝ | -c ≤ y}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), hmap]
        rfl
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (hch.trans_eq ?_)
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        have hσ2 : σ ^ 2 ≠ 0 := by positivity
        field_simp
        ring

/-- **`E[T_c] < ∞`** for the down-drift process. -/
theorem lintegral_hitLevel_lt_top (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) : ∫⁻ ω, (hitLevel (dpath σ (-μ) b ω) (-c) : ℝ≥0∞) ∂P < ∞ := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hTm := measurable_hitLevel_dpath hb σ (-μ) (-c)
  have e : ∀ ω, (hitLevel (dpath σ (-μ) b ω) (-c) : ℝ≥0∞)
      = ENNReal.ofReal (hitLevel (dpath σ (-μ) b ω) (-c) : ℝ) :=
    fun ω => (ENNReal.ofReal_coe_nnreal).symm
  rw [lintegral_congr e, lintegral_eq_lintegral_meas_lt P
    (Eventually.of_forall fun ω => NNReal.coe_nonneg _)
    (measurable_coe_nnreal_real.comp hTm).aemeasurable]
  have hb' : 0 < μ ^ 2 / (2 * σ ^ 2) := by positivity
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
    (g := fun m => ENNReal.ofReal (Real.exp (μ * c / σ ^ 2)
      * Real.exp (-(μ ^ 2 / (2 * σ ^ 2)) * m))) fun m hm => ?_) ?_
  · refine (measure_mono fun ω hω => ?_).trans (measure_dpath_ge_le hb hσ hμ c hm)
    have hlt : m.toNNReal < hitLevel (dpath σ (-μ) b ω) (-c) :=
      (Real.toNNReal_lt_iff_lt_coe (le_of_lt hm)).2 hω
    exact (hitLevel_lt_of_neg (continuous_dpath hb σ (-μ) ω) (dpath_zero hb σ (-μ) ω)
      (neg_lt_zero.2 hc) hlt).le
  · exact ((exp_neg_integrableOn_Ioi 0 hb').const_mul _).lintegral_lt_top

end QuantumZipper.Williams
