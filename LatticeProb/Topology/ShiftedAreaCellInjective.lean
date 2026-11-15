import LatticeProb.Analysis.AreaParametrizedCurveCells
import LatticeProb.Topology.CompactCurveRange
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Distinct shifted cells of an area-parametrized curve -/

set_option autoImplicit false

open MeasureTheory Set TopologicalSpace

namespace LatticeProb

/-- Positive-mesh shifted cells of an area-parametrized curve are distinct. -/
theorem shiftedCompactCell_injective_of_areaParametrized
    {μ : Measure ℂ} (η : C(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (θ : ℝ)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a)) :
    Function.Injective (shiftedCompactCell η ε θ) := by
  intro j k heq
  by_contra hjk
  have hends (i : ℤ) : ε * ((i : ℝ) - 1 + θ) < ε * ((i : ℝ) + θ) :=
    mul_lt_mul_of_pos_left (by linarith) hε
  have hmass : 0 < μ (shiftedCompactCell η ε θ j : Set ℂ) := by
    rw [coe_shiftedCompactCell, uIcc_of_le (hends j).le, hμ _ _ (hends j)]
    apply ENNReal.ofReal_pos.mpr
    nlinarith
  have hnull : μ ((shiftedCompactCell η ε θ j : Set ℂ) ∩
      (shiftedCompactCell η ε θ k : Set ℂ)) = 0 := by
    simp only [coe_shiftedCompactCell, uIcc_of_le (hends _).le]
    rcases lt_or_gt_of_ne hjk with hjk' | hkj
    · have hle : (j : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.mpr hjk'
      exact measure_image_Icc_inter_image_Icc_eq_zero η.continuous hμ (hends j)
        (mul_le_mul_of_nonneg_left (by linarith) hε.le) (hends k)
    · rw [inter_comm]
      have hle : (k : ℝ) + 1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hkj
      exact measure_image_Icc_inter_image_Icc_eq_zero η.continuous hμ (hends k)
        (mul_le_mul_of_nonneg_left (by linarith) hε.le) (hends j)
  have hset := congrArg (fun K : NonemptyCompacts ℂ => (K : Set ℂ)) heq
  rw [← hset, inter_self] at hnull
  exact (ne_of_gt hmass) hnull

end LatticeProb
