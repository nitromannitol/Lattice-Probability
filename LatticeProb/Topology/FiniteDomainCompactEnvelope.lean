import Mathlib.Topology.MetricSpace.Thickening

/-! # Compact envelopes for finitely many bounded domains -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- A bounded set and finitely many bounded domains admit one compact envelope,
including the closure of each domain. -/
theorem exists_compact_envelope_of_finite_domains
    {X : Type*} [MetricSpace X] [ProperSpace X] {J : Type*} [Finite J]
    {D : Set X} (hD : Bornology.IsBounded D)
    (W : J → Set X) (hW : ∀ j, Bornology.IsBounded (W j)) :
    ∃ C : Set X, IsCompact C ∧ D ⊆ C ∧ ∀ j, closure (W j) ⊆ C := by
  let V := D ∪ ⋃ j, W j
  have hV : Bornology.IsBounded V := hD.union (Bornology.isBounded_iUnion.mpr hW)
  refine ⟨closure V, hV.isCompact_closure, ?_, ?_⟩
  · exact (subset_union_left : D ⊆ V).trans subset_closure
  · intro j
    exact closure_mono (fun x hx => Or.inr (mem_iUnion.mpr ⟨j, hx⟩))

/-- A bounded set's thickening and finitely many bounded domains admit a common
compact envelope. The envelope can be chosen before any later finite horizon. -/
theorem exists_compact_envelope_thickening_of_finite_domains
    {X : Type*} [MetricSpace X] [ProperSpace X] {J : Type*} [Finite J]
    {U : Set X} (hU : Bornology.IsBounded U) (δ : ℝ)
    (W : J → Set X) (hW : ∀ j, Bornology.IsBounded (W j)) :
    ∃ C : Set X, IsCompact C ∧ thickening δ U ⊆ C ∧ ∀ j, closure (W j) ⊆ C :=
  exists_compact_envelope_of_finite_domains hU.thickening W hW

end LatticeProb
