import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Interfaces
import LatticeProb.LQG.GMCRatioLimit

/-! # Dyadic bounds for circle averages -/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

/-- A circle-average supremum tail gives a simultaneous spatial bound at all
sufficiently small dyadic radii, for each fixed error and spatial radius. -/
theorem ae_eventually_dyadic_circle_sup_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ)
    (hH : MatedCRTHarmonic.GMS4b.CircleAverageSupBound P H)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ z ∈ ball (0 : ℂ) ρ,
      |H (dyadicScale k) z ω| ≤ (2 + δ) * Real.log (dyadicScale k)⁻¹ := by
  obtain ⟨β, hβ, htail⟩ := hH δ hδ
  obtain ⟨C, hC⟩ := htail ρ hρ
  let E : ℕ → Set Ω := fun k => {ω | ∃ z ∈ ball (0 : ℂ) ρ,
    (2 + δ) * Real.log (dyadicScale (k + 1))⁻¹ < |H (dyadicScale (k + 1)) z ω|}
  have hbound : ∀ k, P (E k) ≤ ENNReal.ofReal (|C| * dyadicScale (k + 1) ^ β) := by
    intro k
    have hr : dyadicScale (k + 1) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact pow_pos (by norm_num) _
      · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact (hC _ hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hr.1.le _)))
  have hsm : Summable (fun k : ℕ => |C| * dyadicScale (k + 1) ^ β) :=
    ((summable_nat_add_iff 1).2 (GMCRatioLimit.summable_dyadicScale_rpow hβ)).mul_left _
  have hfin : ∑' k, P (E k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (abs_nonneg C)
      (Real.rpow_nonneg (show 0 ≤ dyadicScale (k + 1) from (pow_pos (by norm_num) _).le) _)) hsm]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  apply eventually_atTop.2
  refine ⟨N + 1, fun k hk z hz => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact not_lt.1 (fun h => hN j (by omega) ⟨z, hz, h⟩)

end LatticeProb.LQG
