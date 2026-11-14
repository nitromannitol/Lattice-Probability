import LatticeProb.Prob.NormalizedPathPrefix

/-! # Clipped normalized clocks -/

set_option autoImplicit false
open scoped NNReal unitInterval

namespace LatticeProb

/-- Clip a nonnegative clock at a positive duration and normalize it to the unit interval. -/
noncomputable def clippedPrefixClock (h : C(unitInterval, ℝ≥0)) (T : ℝ≥0)
    (hT : 0 < T) : C(unitInterval, unitInterval) :=
  ⟨fun u => ⟨(min (h u) T : ℝ) / (T : ℝ), by
      constructor
      · exact div_nonneg (min (h u) T).property (NNReal.coe_nonneg T)
      · apply (div_le_one (by exact_mod_cast hT)).mpr
        exact_mod_cast min_le_right (h u) T⟩,
    by fun_prop⟩

lemma clippedPrefixClock_monotone (h : C(unitInterval, ℝ≥0)) (T : ℝ≥0)
    (hT : 0 < T) (hh : Monotone h) : Monotone (clippedPrefixClock h T hT) := by
  intro u v huv
  change (min (h u) T : ℝ) / (T : ℝ) ≤ (min (h v) T : ℝ) / (T : ℝ)
  apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg T)
  exact_mod_cast min_le_min_right T (hh huv)

lemma clippedPrefixClock_zero (h : C(unitInterval, ℝ≥0)) (T : ℝ≥0)
    (hT : 0 < T) (hh : h 0 = 0) : clippedPrefixClock h T hT 0 = 0 := by
  apply Subtype.ext
  change (min (h 0) T : ℝ) / (T : ℝ) = 0
  simp only [hh, NNReal.coe_zero, min_eq_left (NNReal.coe_nonneg T), zero_div]

lemma clippedPrefixClock_one (h : C(unitInterval, ℝ≥0)) (T : ℝ≥0)
    (hT : 0 < T) (hh : T ≤ h 1) : clippedPrefixClock h T hT 1 = 1 := by
  apply Subtype.ext
  change (min (h 1) T : ℝ) / (T : ℝ) = 1
  have hhreal : (T : ℝ) ≤ (h 1 : ℝ) := by exact_mod_cast hh
  rw [min_eq_right hhreal]
  exact div_self (by exact_mod_cast hT.ne')

lemma mul_clippedPrefixClock (h : C(unitInterval, ℝ≥0)) (T : ℝ≥0)
    (hT : 0 < T) (u : unitInterval) :
    (T : ℝ) * (clippedPrefixClock h T hT u : ℝ) = (min (h u) T : ℝ) := by
  change (T : ℝ) * ((min (h u) T : ℝ) / (T : ℝ)) = _
  exact mul_div_cancel₀ _ (by exact_mod_cast hT.ne')

end LatticeProb
