import LatticeProb.Topology.FrontierArcComponent
import LatticeProb.Topology.FiniteComponentCardinality
import LatticeProb.Topology.ConnectedWitnessComponentCount

/-! # Counting components containing shared frontier arcs -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- Distinct components containing shared frontier arcs give a lower bound for
    the extended number of non-singleton intersection components. -/
theorem le_encard_nonSingletonComponents_of_shared_frontier_arcs
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (n : ℕ)
    (p : Fin n → C(unitInterval, X))
    (hp : ∀ i, Function.Injective (p i))
    (hAp : ∀ i t, p i t ∈ frontier A) (hBp : ∀ i t, p i t ∈ frontier B)
    (hsep : Function.Injective (fun i => connectedComponentIn (A ∩ B) (p i 0))) :
    (n : ℕ∞) ≤ (nonSingletonComponents (A ∩ B)).encard := by
  apply (Topology.le_encard_nonSingletonComponents_iff (A ∩ B) n).2
  refine ⟨fun i => p i 0, ?_, hsep, ?_⟩
  · intro i
    exact ⟨hA.frontier_subset (hAp i 0), hB.frontier_subset (hBp i 0)⟩
  · intro i
    obtain ⟨C, ⟨x, hx, hC⟩, hn, hsub⟩ :=
      exists_nonSingleton_inter_component_of_shared_frontier_arc hA hB (p i) (hp i)
        (hAp i) (hBp i)
    have h0 : p i 0 ∈ C := hsub ⟨0, rfl⟩
    have h0' : p i 0 ∈ connectedComponentIn (A ∩ B) x := by
      rw [hC]
      exact h0
    rw [(connectedComponentIn_eq h0').symm, hC]
    exact hn

/-- Shared frontier arcs count all non-singleton intersection components when
    they lie in distinct components and every such component contains an arc. -/
theorem ncard_nonSingletonComponents_eq_of_shared_frontier_arcs
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (n : ℕ)
    (p : Fin n → C(unitInterval, X))
    (hp : ∀ i, Function.Injective (p i))
    (hAp : ∀ i t, p i t ∈ frontier A) (hBp : ∀ i t, p i t ∈ frontier B)
    (hsep : Function.Injective (fun i => connectedComponentIn (A ∩ B) (p i 0)))
    (hcover : ∀ x ∈ A ∩ B, ¬ (connectedComponentIn (A ∩ B) x).Subsingleton →
      ∃ i, range (p i) ⊆ connectedComponentIn (A ∩ B) x) :
    (nonSingletonComponents (A ∩ B)).ncard = n := by
  have hsub (i : Fin n) : range (p i) ⊆ A ∩ B := by
    rintro _ ⟨t, rfl⟩
    exact ⟨hA.frontier_subset (hAp i t), hB.frontier_subset (hBp i t)⟩
  have hn (i : Fin n) : ¬ (range (p i)).Subsingleton := by
    intro h
    have : (0 : unitInterval) = 1 := hp i (h ⟨0, rfl⟩ ⟨1, rfl⟩)
    exact zero_ne_one this
  simpa only [nonSingletonComponents, Nat.card_fin] using
    ncard_nonSingletonComponents_eq_card_witnesses (A ∩ B) (fun i => range (p i))
      (fun i => p i 0) (fun _ => ⟨0, rfl⟩)
      (fun i => isPreconnected_range (p i).continuous) hsub hn hsep hcover

end LatticeProb
