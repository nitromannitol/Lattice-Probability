import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-! # Comparison of a cell walk and its holding-time interpolation -/

set_option autoImplicit false

open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigStepInterpolation

/-- On a holding interval the interpolation differs from the step walk by at
most the length of the next jump. -/
theorem dist_interpolatedPath_walk_le (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    {n : ℕ} {s : ℝ} (h1 : H.jumpTime ω n ≤ s)
    (h2 : s < H.jumpTime ω (n + 1)) :
    dist (H.interpolatedPath p ω s) (p (H.walk ω s)) ≤
      dist (p (ω n)) (p (ω (n + 1))) := by
  rw [H.walk_eq_of_mem hpos h1 h2, H.interpolatedPath_eq_lineMap hpos h1 h2.le,
    dist_lineMap_left]
  have hd : 0 < H.jumpTime ω (n + 1) - H.jumpTime ω n :=
    sub_pos.mpr (H.jumpTime_strictMono hpos (Nat.lt_succ_self n))
  have h0 : 0 ≤ (s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n) :=
    div_nonneg (sub_nonneg.mpr h1) hd.le
  have hle : (s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n) ≤ 1 := by
    rw [div_le_one hd]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left dist_nonneg hle

/-- A common bound on jumps started by time `S` bounds the step/interpolation
error throughout the interval from zero to `S`. -/
theorem dist_interpolatedPath_walk_le_of_jump_bound
    (H : CellConfig) (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (S δ : ℝ) (hjump : ∀ n, H.jumpTime ω n ≤ S →
      dist (p (ω n)) (p (ω (n + 1))) ≤ δ) :
    ∀ s : ℝ, 0 ≤ s → s ≤ S →
      dist (H.interpolatedPath p ω s) (p (H.walk ω s)) ≤ δ := by
  intro s hs hsS
  obtain ⟨n, hn, hn'⟩ := H.exists_mem_Ico hpos hunb hs
  exact (dist_interpolatedPath_walk_le H p ω hpos hn hn').trans (hjump n (hn.trans hsS))

end LatticeProb.CellConfigStepInterpolation
