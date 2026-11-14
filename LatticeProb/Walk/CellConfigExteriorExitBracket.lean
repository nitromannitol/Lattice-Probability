import LatticeProb.Walk.CellConfigFiniteExit
import LatticeProb.Walk.CellConfigInterpolationDiameter
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionRange

/-!
# First exterior vertex and interpolated exit

For a convex domain, the first exterior representative is reached on the edge
containing the exit of the linearly interpolated walk.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- If all scaled representatives through index `n` are inside a convex domain,
then the walk remains inside up to the `n`th scaled jump. -/
theorem interpolatedWalk_mem_through_jump_of_representatives (H : CellConfig)
    (p : H.cells → Plane) (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) {ε : ℝ≥0} (hε : 0 < ε)
    {U : Set Plane} (hconv : Convex ℝ U) (n : ℕ)
    (hin : ∀ j ≤ n, (ε : ℝ) • p (ω j) ∈ U) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω n) :
    H.interpolatedWalk p ε ω t ∈ U := by
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  have htn : (t : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω n := by
    apply (div_le_iff₀ he).2
    simpa only [mul_comm] using ht
  obtain ⟨j, hj, hj'⟩ := H.exists_mem_Ico hpos hunb
    (div_nonneg t.property (sq_nonneg (ε : ℝ)))
  have hjn : j ≤ n := by
    by_contra h
    have hm := H.jumpTime_strictMono (ω := ω) hpos (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge (hj.trans htn)) hm
  by_cases h : j = n
  · subst j
    have ht' : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω n := by
      have : (t : ℝ) / (ε : ℝ) ^ 2 = H.jumpTime ω n := le_antisymm htn hj
      simpa only [mul_comm] using (div_eq_iff he.ne').mp this
    have teq : t = ⟨(ε : ℝ) ^ 2 * H.jumpTime ω n,
        mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos n)⟩ := by
      apply Subtype.ext
      exact ht'
    rw [teq, interpolatedWalk_at_jumpTime H p ω hpos hunb n hε]
    exact hin n le_rfl
  · have hjlt : j < n := lt_of_le_of_ne hjn h
    have hd : 0 < H.jumpTime ω (j + 1) - H.jumpTime ω j := by
      rw [H.jumpTime_succ]
      simpa using hpos (ω j)
    let u : ℝ := ((t : ℝ) / (ε : ℝ) ^ 2 - H.jumpTime ω j) /
      (H.jumpTime ω (j + 1) - H.jumpTime ω j)
    have hu : u ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr hj) hd.le,
      (div_le_one hd).2 (sub_le_sub_right hj'.le _)⟩
    have hm := hconv.lineMap_mem (hin j hjn) (hin (j + 1) (Nat.succ_le_of_lt hjlt)) hu
    have hl : H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) =
        AffineMap.lineMap (p (ω j)) (p (ω (j + 1))) u :=
      H.interpolatedPath_eq_lineMap hpos hj hj'.le
    rw [show H.interpolatedWalk p ε ω t =
        (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
        congrFun (H.coe_interpolatedWalk hpos hunb ε) t, hl]
    simpa only [AffineMap.lineMap_apply_module, smul_add, smul_smul, mul_comm] using hm

/-- If the first exterior representative occurs at `n + 1`, the exit is after
jump `n`, no later than jump `n + 1`, and close to that exterior representative. -/
theorem continuousExitTime_bracket_of_first_exterior (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (n : ℕ) (hadj : H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : IsOpen U)
    (hconv : Convex ℝ U)
    (hin : ∀ j ≤ n, (ε : ℝ) • p (ω j) ∈ U)
    (hout : (ε : ℝ) • p (ω (n + 1)) ∉ U) :
    let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
    τ ≠ ∞ ∧
    (ε : ℝ) ^ 2 * H.jumpTime ω n < (τ.toNNReal : ℝ) ∧
    (τ.toNNReal : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) ∧
    dist ((H.interpolatedWalk p ε ω) τ.toNNReal) ((ε : ℝ) • p (ω (n + 1))) ≤
      (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane)) := by
  let t (k : ℕ) : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω k,
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos k)⟩
  let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
  have hfin : τ ≠ ∞ := continuousExitTime_ne_top_of_visit H p ω hpos hunb hε U (n + 1) hout
  have hlow : (t n : ℝ≥0∞) < τ := by
    apply lt_continuousExitTime_of_mem_Icc hU
    intro s hs
    simp only [zero_add]
    apply interpolatedWalk_mem_through_jump_of_representatives H p ω hpos hunb hε hconv n hin s
    exact_mod_cast hs.2
  have hupp : τ ≤ (t (n + 1) : ℝ≥0∞) := by
    apply continuousExitTime_le_of_not_mem
    simp only [zero_add]
    change H.interpolatedWalk p ε ω ⟨_, _⟩ ∉ U
    rw [interpolatedWalk_at_jumpTime H p ω hpos hunb (n + 1) hε]
    exact hout
  have hl : (ε : ℝ) ^ 2 * H.jumpTime ω n < (τ.toNNReal : ℝ) := by
    have h := hlow
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  have hu : (τ.toNNReal : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) := by
    have h := hupp
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe] at h
    exact_mod_cast h
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  have h1 : H.jumpTime ω n ≤ (τ.toNNReal : ℝ) / (ε : ℝ) ^ 2 := by
    apply (le_div_iff₀ he).2
    simpa only [mul_comm] using hl.le
  have h2 : (τ.toNNReal : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω (n + 1) := by
    apply (div_le_iff₀ he).2
    simpa only [mul_comm] using hu
  have hb := (dist_interpolatedPath_endpoints_le H hH p hp ω hpos h1 h2 hadj).2
  refine ⟨hfin, hl, hu, ?_⟩
  rw [show H.interpolatedWalk p ε ω τ.toNNReal =
      (ε : ℝ) • H.interpolatedPath p ω ((τ.toNNReal : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) τ.toNNReal]
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
    ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left hb ε.coe_nonneg

end LatticeProb.CellConfigInterpolation
end
