import LatticeProb.Walk.CellConfigInterpolationShift
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRestart

/-!
# Exit positions after restarting an interpolated walk

A finite exit position is unchanged when a continuous path is restarted no later
than its exit. The same principle applies at a jump of an interpolated cell walk.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A path and its time-shift have the same finite exit position. -/
theorem exitPosition_eq_of_shift {d : ℕ} (U : Set (Euc d))
    (γ δ : BrownianPath d) (t : ℝ≥0) (hshift : ∀ s, δ s = γ (t + s))
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime U 0 γ)
    (hfin : continuousExitTime U 0 γ ≠ ∞) :
    δ (continuousExitTime U 0 δ).toNNReal = γ (continuousExitTime U 0 γ).toNNReal := by
  have hpred : (fun s : ℝ≥0 => (0 : Euc d) + δ s ∉ U) =
      (fun s : ℝ≥0 => (0 + γ t) + shiftedBrownianPath t γ s ∉ U) := by
    funext s
    simp only [zero_add, shiftedBrownianPath, ContinuousMap.coe_mk]
    rw [hshift s]
    congr 1
    abel
  have hexit : continuousExitTime U 0 δ =
      continuousExitTime U (0 + γ t) (shiftedBrownianPath t γ) := by
    unfold continuousExitTime
    rw [hpred]
  have hend := continuousExitTime_shift_endpoint U 0 γ t ht hfin
  rw [hexit, hshift]
  simpa only [zero_add, shiftedBrownianPath, ContinuousMap.coe_mk, add_sub_cancel] using hend

/-- An unbounded jump clock remains unbounded after a finite number of jumps. -/
theorem jumpTimesUnbounded_shift (H : CellConfig) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω) (k : ℕ) :
    H.JumpTimesUnbounded (fun j => ω (k + j)) := by
  intro N
  obtain ⟨m, hm⟩ := exists_nat_gt ((N : ℝ) + H.jumpTime ω k)
  obtain ⟨n, hn⟩ := hunb m
  have hkn : k ≤ n := by
    by_contra h
    have hmono := (H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_of_lt (Nat.lt_of_not_ge h))
    linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  refine ⟨j, ?_⟩
  rw [jumpTime_add] at hn
  linarith

/-- Rescaled interpolation commutes with restarting the cell sequence at a jump. -/
theorem interpolatedWalk_jumpTime_add (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (k : ℕ)
    {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ≥0)
    (ht : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω k) (s : ℝ≥0) :
    H.interpolatedWalk p ε (fun j => ω (k + j)) s =
      H.interpolatedWalk p ε ω (t + s) := by
  have he : (ε : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  have htime : ((t + s : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2 =
      H.jumpTime ω k + (s : ℝ) / (ε : ℝ) ^ 2 := by
    rw [NNReal.coe_add, ht]
    field_simp
  rw [show (H.interpolatedWalk p ε (fun j => ω (k + j))) s =
      (ε : ℝ) • H.interpolatedPath p (fun j => ω (k + j)) ((s : ℝ) / (ε : ℝ) ^ 2) by
        exact congrFun (H.coe_interpolatedWalk hpos (jumpTimesUnbounded_shift H ω hpos hunb k) ε) s,
      show (H.interpolatedWalk p ε ω) (t + s) =
      (ε : ℝ) • H.interpolatedPath p ω (((t + s : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2) by
        exact congrFun (H.coe_interpolatedWalk hpos hunb ε) (t + s), htime,
      interpolatedPath_jumpTime_add H p ω hpos hunb k
        (t := (s : ℝ) / (ε : ℝ) ^ 2) (div_nonneg s.property (sq_nonneg _))]

/-- Restarting at a jump before a finite exit preserves the exit position. -/
theorem interpolatedWalk_exitPosition_restart (H : CellConfig) (p : H.cells → Plane)
    (ω : ℕ → H.cells) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (k : ℕ)
    {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ≥0)
    (ht : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω k) (U : Set Plane)
    (hbefore : (t : ℝ≥0∞) ≤ continuousExitTime U 0 (H.interpolatedWalk p ε ω))
    (hfin : continuousExitTime U 0 (H.interpolatedWalk p ε ω) ≠ ∞) :
    (H.interpolatedWalk p ε (fun j => ω (k + j)))
        (continuousExitTime U 0 (H.interpolatedWalk p ε (fun j => ω (k + j)))).toNNReal =
      (H.interpolatedWalk p ε ω)
        (continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal :=
  exitPosition_eq_of_shift U _ _ t
    (interpolatedWalk_jumpTime_add H p ω hpos hunb k hε t ht) hbefore hfin

end LatticeProb.CellConfigInterpolation
