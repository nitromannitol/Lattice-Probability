import LatticeProb.Walk.CellConfigInnerBoundary
import LatticeProb.Walk.CellConfigExitRestart
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionRange

/-!
# Inner-boundary confinement and exit restart

A rescaled interpolated cell walk remains in an outer domain through a jump
reaching an inner boundary, provided the cells along that segment are confined.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Confinement through an inner-boundary jump puts the scaled jump time strictly
before the first exit from an open outer domain. -/
theorem scaled_jumpTime_lt_exit_of_inner_boundary (H : CellConfig)
    (hH : H.IsCellConfiguration) {U V W : Set Plane}
    (hV : IsOpen V) (hVU : V ⊆ U) (hconv : Convex ℝ U) (hW : IsOpen W)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (ω : ℕ → H.cells) (hstart : (((ω 0).1 : Set Plane) ∩ V).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (k : ℕ)
    (havoid : ∀ j < k, ¬ (((ω j).1 : Set Plane) ∩ frontier V).Nonempty)
    (hlast : ((ω k).1 : Set Plane) ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε) (hscale : ∀ z ∈ U, (ε : ℝ) • z ∈ W)
    (t : ℝ≥0) (ht : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω k) :
    (t : ℝ≥0∞) < continuousExitTime W 0 (H.interpolatedWalk p ε ω) := by
  apply lt_continuousExitTime_of_mem_Icc hW
  intro s hs
  simp only [zero_add]
  rw [show (H.interpolatedWalk p ε ω) s =
      (ε : ℝ) • H.interpolatedPath p ω ((s : ℝ) / (ε : ℝ) ^ 2) by
    exact congrFun (H.coe_interpolatedWalk hpos hunb ε) s]
  apply hscale
  apply LatticeProb.CellConfigBoundary.interpolatedPath_mem_through_inner_boundary H
    hH hV hVU hconv p hp ω hstart hadj hpos hunb
    (div_nonneg s.property (sq_nonneg _))
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  apply (div_le_iff₀ he).2
  have hs' : (s : ℝ) ≤ t := by exact_mod_cast hs.2
  rw [ht] at hs'
  rw [mul_comm]
  exact hs'
  all_goals assumption

/-- The exit position is preserved when restarting at the confined jump. -/
theorem exitPosition_restart_of_inner_boundary (H : CellConfig)
    (hH : H.IsCellConfiguration) {U V W : Set Plane}
    (hV : IsOpen V) (hVU : V ⊆ U) (hconv : Convex ℝ U) (hW : IsOpen W)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (ω : ℕ → H.cells) (hstart : (((ω 0).1 : Set Plane) ∩ V).Nonempty)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1))) (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) (k : ℕ)
    (havoid : ∀ j < k, ¬ (((ω j).1 : Set Plane) ∩ frontier V).Nonempty)
    (hlast : ((ω k).1 : Set Plane) ⊆ U)
    {ε : ℝ≥0} (hε : 0 < ε) (hscale : ∀ z ∈ U, (ε : ℝ) • z ∈ W)
    (t : ℝ≥0) (ht : (t : ℝ) = (ε : ℝ) ^ 2 * H.jumpTime ω k)
    (hfin : continuousExitTime W 0 (H.interpolatedWalk p ε ω) ≠ ∞) :
    (H.interpolatedWalk p ε (fun j => ω (k + j)))
        (continuousExitTime W 0 (H.interpolatedWalk p ε (fun j => ω (k + j)))).toNNReal =
      (H.interpolatedWalk p ε ω)
        (continuousExitTime W 0 (H.interpolatedWalk p ε ω)).toNNReal :=
  interpolatedWalk_exitPosition_restart H p ω hpos hunb k hε t ht W
    (scaled_jumpTime_lt_exit_of_inner_boundary H hH hV hVU hconv hW p hp ω hstart
      hadj hpos hunb k havoid hlast hε hscale t ht).le hfin

end LatticeProb.CellConfigInterpolation

end
