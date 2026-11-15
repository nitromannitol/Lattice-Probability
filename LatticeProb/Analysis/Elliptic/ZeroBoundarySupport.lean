import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.OrderClosed

/-!
# Compact superlevel sets for zero boundary values

A continuous function vanishing on the boundary of a bounded open set has compact
positive superlevel sets contained in the set.
-/

open scoped Topology

namespace LatticeProb.Elliptic.WeakDirichlet

variable {d : ℕ} {U : Set (Fin d → ℝ)}

/-- Positive absolute-value superlevel sets are compactly contained in the domain. -/
theorem superlevel_compact (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (u : (Fin d → ℝ) → ℝ) (hu : ContinuousOn u (closure U))
    (hz : Set.EqOn u (fun _ => 0) (frontier U)) (ε : ℝ) (hε : 0 < ε) :
    IsCompact {x ∈ closure U | ε ≤ |u x|} ∧
      {x ∈ closure U | ε ≤ |u x|} ⊆ U := by
  constructor
  · exact hb.isCompact_closure.of_isClosed_subset
      (isClosed_closure.isClosed_le continuousOn_const hu.abs) (fun _ hx => hx.1)
  · intro x hx
    by_contra hxU
    have hfront : x ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hx.1, hxU⟩
    have hz' : u x = 0 := hz hfront
    have : ε ≤ 0 := by simpa [hz'] using hx.2
    exact (not_le_of_gt hε) this

end LatticeProb.Elliptic.WeakDirichlet
