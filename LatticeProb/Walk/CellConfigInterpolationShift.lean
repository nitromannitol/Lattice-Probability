import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# Restarting a cell walk's interpolation

The clock and the interpolated path restart at each jump of a cell walk with positive
holding times and an unbounded clock.
-/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigInterpolation

variable (H : CellConfig)

/-- The clock after a jump is the clock of the shifted cell sequence. -/
theorem jumpTime_add (ω : ℕ → H.cells) (k n : ℕ) :
    H.jumpTime ω (k + n) = H.jumpTime ω k + H.jumpTime (fun j => ω (k + j)) n := by
  induction n with
  | zero => simp [CellConfig.jumpTime_zero]
  | succ n ih =>
    rw [Nat.add_succ, CellConfig.jumpTime_succ, CellConfig.jumpTime_succ, ih]
    ring

/-- At a jump time, the future interpolated path is the interpolation of the shifted
sequence. The assertion includes the zeroth jump and the initial time. -/
theorem interpolatedPath_jumpTime_add (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    H.interpolatedPath p ω (H.jumpTime ω k + t) =
      H.interpolatedPath p (fun j => ω (k + j)) t := by
  obtain ⟨j, hj1, hj2⟩ := H.exists_mem_Ico hpos hunb
    (show 0 ≤ H.jumpTime ω k + t from add_nonneg (H.jumpTime_nonneg hpos k) ht)
  have hkj : k ≤ j := by
    by_contra h
    have hk := (H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
    linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have hshift1 : H.jumpTime (fun j => ω (k + j)) n ≤ t := by
    have heq := jumpTime_add H ω k n
    linarith
  have hshift2 : t < H.jumpTime (fun j => ω (k + j)) (n + 1) := by
    have heq := jumpTime_add H ω k (n + 1)
    have heqidx : k + n + 1 = k + (n + 1) := by omega
    rw [heqidx] at hj2
    linarith
  rw [H.interpolatedPath_eq_of_mem hpos hj1 hj2,
    H.interpolatedPath_eq_of_mem hpos hshift1 hshift2]
  simp only [CellConfig.affinePiece, jumpTime_add]
  congr 2; ring

end LatticeProb.CellConfigInterpolation

end
