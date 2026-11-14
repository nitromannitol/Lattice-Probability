import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# Scaled affine pieces of cell walks

The scaled walk interpolates the scaled representatives on each scaled jump interval.
-/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- The scaled walk is affine between consecutive scaled jump times. -/
theorem interpolatedWalk_eq_lineMap_of_scaled_jumpTime
    (H : CellConfig) (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {ε : ℝ≥0} (hε : 0 < ε) {n : ℕ} (t : ℝ≥0)
    (h1 : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1)) :
    (H.interpolatedWalk p ε ω) t =
      AffineMap.lineMap ((ε : ℝ) • p (ω n)) ((ε : ℝ) • p (ω (n + 1)))
        (((t : ℝ) - (ε : ℝ) ^ 2 * H.jumpTime ω n) /
          ((ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) -
            (ε : ℝ) ^ 2 * H.jumpTime ω n)) := by
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  have hlow : H.jumpTime ω n ≤ (t : ℝ) / (ε : ℝ) ^ 2 := by
    apply (le_div_iff₀ he).2
    simpa [mul_comm] using h1
  have hhigh : (t : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω (n + 1) :=
    (div_le_iff₀ he).2 (by simpa [mul_comm] using h2)
  rw [show (H.interpolatedWalk p ε ω) t =
      (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) t,
    H.interpolatedPath_eq_lineMap hpos hlow hhigh]
  have hratio : ((t : ℝ) / (ε : ℝ) ^ 2 - H.jumpTime ω n) /
      (H.jumpTime ω (n + 1) - H.jumpTime ω n) =
      ((t : ℝ) - (ε : ℝ) ^ 2 * H.jumpTime ω n) /
        ((ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) -
          (ε : ℝ) ^ 2 * H.jumpTime ω n) := by
    have hd : H.jumpTime ω (n + 1) - H.jumpTime ω n ≠ 0 := by
      rw [H.jumpTime_succ]
      simpa using (hpos (ω n)).ne'
    have hd' : (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) -
        (ε : ℝ) ^ 2 * H.jumpTime ω n ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero he.ne' hd
    field_simp
  rw [hratio]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_sub, smul_add,
    smul_smul]
  congr 1
  rw [mul_comm]

end LatticeProb.CellConfigInterpolation

end
