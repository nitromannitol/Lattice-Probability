/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13Real at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Layer
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T13Energy
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.FixedInstance
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelFinal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsASource
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsALemma27

/-!
# Real meshes `ε ∈ (0, 1)`: asymptotics, admissibility, the rate helper and (1.8)

The [18] results are stated for every real `ε ∈ (0, 1)`. The real-mesh inputs hold
for the mated-CRT map `MatedCRT.graph ε (bm ω)` of every frozen coupling with the curve cells `η ω([ε(x−1), εx])`:
[18] Proposition 2.10 (`GMSMain.epsA_prop210Source`, bad event `GMSMain.EpsAProp210Bad`) and Lemma 2.7
(`GMSMain.epsA_lemma27Bad_coupling`, bad event `GMSMain.EpsALemma27Bad`). Both bad events are the failure of "an
embedding with the curve cells exists, and EVERY such embedding satisfies the bound". This file:

* `t13r_tendsto_rpow`, `t13r_tendsto_rpow_div_pow`, `t13r_tendsto_log_div_rpow`, **`t13r_tendsto_lemma34Bound_mul_log`**
  — the asymptotics of `T13Theorem14` along `ε → 0+` (`𝓝[>] 0`) instead of dyadic sequences;
* `t13r_threeAdmissible` — the three tests of Lemma 3.4 are admissible for Proposition 2.10 at a real mesh;
* **`t13r_rate_of_eventually`** — a failure bound `≤ K ε^α` for all small `ε`, uniform in a parameter, gives
  `≤ C ε^α` for every `ε ∈ (0, 1)` (coarse meshes absorbed into `C`);
* `T13RealGreenGood ε ρ A b c` — the event (1.8) for the mated-CRT map of `b` with the cells of `c`;
* **`t13r_green_of_inputs`** — (1.8) at every real mesh from the two named real-mesh inputs (Lemma 2.7 on `B_{ρ₁}`,
  Proposition 2.10 at `(ρ₁, 100, β_G)`) in their stated forms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-! ### Asymptotics along `ε → 0+` -/

theorem t13r_tendsto_rpow {a : ℝ} (ha : 0 < a) : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Admissibility of the Lemma 3.4 tests at a real mesh -/

/-! ### The rate helper -/

/-- **Coarse meshes absorbed into the rate**: if, for all small real `ε > 0`, the failure probabilities of a family of
events indexed by `i` with `Q ε i` are `≤ K ε^α`, then for some `C ≥ 0` they are `≤ C ε^α` for every `ε ∈ (0, 1)`.
`C` depends only on `K`, `α` and the threshold, not on `i`. -/
theorem t13r_rate_of_eventually {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} {Q : ℝ → ι → Prop} {Bad : ℝ → ι → Set Ω} {K α : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, Q ε i → P (Bad ε i) ≤ ENNReal.ofReal (K * ε ^ α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ i, Q ε i → P (Bad ε i) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set ε₁ := min u 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hu one_pos
  have hpos : 0 < ε₁ ^ α := Real.rpow_pos_of_pos hε₁0 α
  refine ⟨K + (ε₁ ^ α)⁻¹, by positivity, fun ε hε i hi => ?_⟩
  have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε.1.le α
  rcases lt_or_ge ε u with h | h
  · refine (hsub ⟨hε.1, h⟩ i hi).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ (ε₁ ^ α)⁻¹ * ε ^ α := by positivity
    nlinarith
  · have hge : ε₁ ^ α ≤ ε ^ α :=
      Real.rpow_le_rpow hε₁0.le ((min_le_left _ _).trans h) hα.le
    have hone : (1 : ℝ) ≤ (K + (ε₁ ^ α)⁻¹) * ε ^ α := by
      have h1 : 1 ≤ (ε₁ ^ α)⁻¹ * ε ^ α := by
        calc (1 : ℝ) = (ε₁ ^ α)⁻¹ * ε₁ ^ α := (inv_mul_cancel₀ hpos.ne').symm
          _ ≤ (ε₁ ^ α)⁻¹ * ε ^ α := mul_le_mul_of_nonneg_left hge (inv_pos.2 hpos).le
      have h2 : 0 ≤ K * ε ^ α := mul_nonneg hK hεα
      nlinarith
    calc P (Bad ε i) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((K + (ε₁ ^ α)⁻¹) * ε ^ α) := ENNReal.ofReal_le_ofReal hone

/-! ### (1.8) at every real mesh -/

end MatedCRTHarmonic.GMSMain
