import LatticeProb.Prob.BrownianOpenExit
import Mathlib

/-! # Finite exits for curves escaping compact sets -/

set_option autoImplicit false

open Set Filter Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A curve escaping compact sets exits every relatively compact set in both time directions. -/
theorem openExitTime_ne_top_of_tendsto_cocompact {E : Type*} [TopologicalSpace E]
    (η : ℝ → E) (U K : Set E) (hK : IsCompact K) (hUK : U ⊆ K)
    (hη : Tendsto η (cocompact ℝ) (cocompact E)) (t₀ : ℝ) :
    openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) U () ≠ ⊤ ∧
    openExitTime (fun s (_ : Unit) => η (t₀ - (s : ℝ))) U () ≠ ⊤ := by
  have hmem : η ⁻¹' Kᶜ ∈ cocompact ℝ := hη hK.compl_mem_cocompact
  obtain ⟨C, hC, hCsub⟩ := mem_cocompact.mp hmem
  obtain ⟨M, hM⟩ := hC.bddAbove
  obtain ⟨m, hm⟩ := hC.bddBelow
  let a : ℝ≥0 := ⟨max 0 (M - t₀) + 1, by positivity⟩
  let b : ℝ≥0 := ⟨max 0 (t₀ - m) + 1, by positivity⟩
  have ha : η (t₀ + (a : ℝ)) ∉ U := by
    intro hu
    have hnotC : t₀ + (a : ℝ) ∉ C := by
      intro hc
      have hbound : M < t₀ + (a : ℝ) := by
        change M < t₀ + (max 0 (M - t₀) + 1)
        linarith [le_max_right (0 : ℝ) (M - t₀)]
      exact (not_lt_of_ge (hM hc)) hbound
    exact hCsub hnotC (hUK hu)
  have hb : η (t₀ - (b : ℝ)) ∉ U := by
    intro hu
    have hnotC : t₀ - (b : ℝ) ∉ C := by
      intro hc
      have hbound : t₀ - (b : ℝ) < m := by
        change t₀ - (max 0 (t₀ - m) + 1) < m
        linarith [le_max_right (0 : ℝ) (t₀ - m)]
      exact (not_lt_of_ge (hm hc)) hbound
    exact hCsub hnotC (hUK hu)
  exact ⟨ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem ha),
    ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem hb)⟩

/-- A curve escaping compact sets exits every metric ball in both time directions. -/
theorem openExitTime_ball_ne_top_of_tendsto_cocompact {E : Type*} [MetricSpace E]
    [ProperSpace E] (η : ℝ → E)
    (hη : Tendsto η (cocompact ℝ) (cocompact E)) (t₀ : ℝ) (z : E) (r : ℝ) :
    openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z r) () ≠ ⊤ ∧
    openExitTime (fun s (_ : Unit) => η (t₀ - (s : ℝ))) (ball z r) () ≠ ⊤ :=
  openExitTime_ne_top_of_tendsto_cocompact η _ _ (isCompact_closedBall z r) ball_subset_closedBall hη t₀

end LatticeProb
