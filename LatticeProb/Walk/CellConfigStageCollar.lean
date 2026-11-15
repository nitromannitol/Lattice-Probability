import LatticeProb.Walk.CellConfigStoppedExitCollar

/-! # Collars for intervals of cell-walk jumps -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- An interpolated walk stays near a set containing the representatives before
an interval's final jump. The diameter bound includes the final edge. -/
theorem interpolatedWalk_mem_cthickening_between_jumps (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) (k l : ℕ) (hkl : k < l) (d : ℝ)
    (hin : ∀ j, k ≤ j → j < l → (ε : ℝ) • p (ω j) ∈ U)
    (hd : ∀ j, k ≤ j → j < l → Metric.diam ((ω j).1 : Set Plane) +
      Metric.diam ((ω (j + 1)).1 : Set Plane) ≤ d)
    (t : ℝ≥0) (htlo : (ε : ℝ) ^ 2 * H.jumpTime ω k ≤ (t : ℝ))
    (hthi : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω l) :
    H.interpolatedWalk p ε ω t ∈ Metric.cthickening ((ε : ℝ) * d) U := by
  by_cases ht : (t : ℝ) < (ε : ℝ) ^ 2 * H.jumpTime ω l
  · obtain ⟨j, hjlo, hjhi, hdist, _⟩ :=
      exists_scaled_jumpTime_bracket_dist_le H hH p hp ω hpos hunb hadj hε t
    have hkj : k ≤ j := by
      by_contra h
      have hm := (H.jumpTime_strictMono (ω := ω) hpos).monotone
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
      have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg (ε : ℝ))
      linarith
    have hjl : j < l := by
      by_contra h
      have hm := (H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_of_not_gt h)
      have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg (ε : ℝ))
      linarith
    exact Metric.mem_cthickening_of_dist_le _ _ _ U (hin j hkj hjl)
      (hdist.trans (mul_le_mul_of_nonneg_left (hd j hkj hjl) ε.coe_nonneg))
  · have heq : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω l := le_antisymm hthi (le_of_not_gt ht)
    have htl : t = ⟨(ε : ℝ) ^ 2 * H.jumpTime ω l,
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos l)⟩ := Subtype.ext heq
    rw [htl, interpolatedWalk_at_jumpTime H p ω hpos hunb l hε]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
    have hkj : k ≤ j := by omega
    apply Metric.mem_cthickening_of_dist_le _ ((ε : ℝ) • p (ω j)) _ U
      (hin j hkj (Nat.lt_succ_self j))
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm, dist_comm]
    exact mul_le_mul_of_nonneg_left
      ((dist_representatives_le H hH p hp (hadj j)).trans (hd j hkj (Nat.lt_succ_self j)))
      ε.coe_nonneg

end LatticeProb.CellConfigInterpolation
end
