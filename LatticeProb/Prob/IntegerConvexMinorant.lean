/-
A convex function on the integers dominates a linear function and a positive jump.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.ConvexProduct
import Mathlib.Analysis.Convex.Slope

noncomputable section
namespace LatticeProb.ConvexOrder

/-- The second difference of a convex function at consecutive integers around a point is
nonnegative. -/
theorem convex_integer_gap_nonneg (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    0 ≤ f 1 + f (-1) - 2 * f 0 := by
  have h := hf.secant_mono_aux1 (x := (-1 : ℝ)) (y := 0) (z := 1)
    (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num)
  norm_num only at h
  linarith

/-- A convex function on the integers dominates the linear minorant through `f 0` and
`f (-1)`, plus the jump at `1` once `k ≥ 1`. -/
theorem convex_integer_minorant (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (k : ℤ) :
    f 0 + (k : ℝ) * (f 0 - f (-1)) +
      (if 1 ≤ k then f 1 + f (-1) - 2 * f 0 else 0) ≤ f (k : ℝ) := by
  have hgap := convex_integer_gap_nonneg f hf
  by_cases hk : 1 ≤ k
  · rw [if_pos hk]
    by_cases hk1 : k = 1
    · subst k
      norm_num only [Int.cast_one]
      linarith
    · have hkR : (1 : ℝ) < k := by exact_mod_cast (show (1 : ℤ) < k by omega)
      have h := hf.secant_mono_aux1 (x := (0 : ℝ)) (y := 1) (z := (k : ℝ))
        (Set.mem_univ _) (Set.mem_univ _) (by norm_num) hkR
      norm_num only [sub_zero, one_mul] at h
      nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hkR)) hgap]
  · rw [if_neg hk, add_zero]
    by_cases hk0 : k = 0
    · subst k
      simp
    · by_cases hkm : k = -1
      · subst k
        norm_num only [Int.cast_neg, Int.cast_one]
        linarith
      · have hkR : (k : ℝ) < -1 := by exact_mod_cast (show k < (-1 : ℤ) by omega)
        have h := hf.secant_mono_aux1 (x := (k : ℝ)) (y := -1) (z := 0)
          (Set.mem_univ _) (Set.mem_univ _) hkR (by norm_num)
        norm_num only at h
        nlinarith

end LatticeProb.ConvexOrder
