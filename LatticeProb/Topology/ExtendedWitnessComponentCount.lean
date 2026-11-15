import LatticeProb.Topology.SharedFrontierArcComponentCount

/-! # Extended counts of components from connected witnesses -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped unitInterval

namespace LatticeProb

/-- Finitely many connected, non-singleton witnesses in distinct components
which cover all non-singleton components give their extended cardinality. -/
theorem encard_nonSingletonComponents_eq_of_connected_witnesses
    {X : Type*} [TopologicalSpace X] (S : Set X) (n : ℕ)
    (A : Fin n → Set X) (p : Fin n → X)
    (hp : ∀ i, p i ∈ A i) (hconn : ∀ i, IsPreconnected (A i))
    (hsub : ∀ i, A i ⊆ S) (hnontriv : ∀ i, ¬ (A i).Subsingleton)
    (hsep : Function.Injective (fun i => connectedComponentIn S (p i)))
    (hcover : ∀ x ∈ S, ¬ (connectedComponentIn S x).Subsingleton →
      ∃ i, A i ⊆ connectedComponentIn S x) :
    (nonSingletonComponents S).encard = (n : ℕ∞) := by
  have hfinite : (nonSingletonComponents S).Finite := by
    apply (Set.finite_range (fun i => connectedComponentIn S (p i))).subset
    rintro C ⟨⟨x, hx, rfl⟩, hn⟩
    obtain ⟨i, hi⟩ := hcover x hx hn
    exact ⟨i, (connectedComponentIn_eq (hi (hp i))).symm⟩
  have hc := ncard_nonSingletonComponents_eq_card_witnesses S A p hp hconn hsub
    hnontriv hsep hcover
  rw [hfinite.encard_eq_coe]
  simpa only [nonSingletonComponents, Set.ncard, Nat.card_fin] using congrArg (fun k : ℕ => (k : ℕ∞)) hc

/-- Shared frontier arcs give the extended component count when their components
are distinct and every non-singleton component contains one of the arcs. -/
theorem encard_nonSingletonComponents_eq_of_shared_frontier_arcs
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (n : ℕ)
    (p : Fin n → C(unitInterval, X))
    (hp : ∀ i, Function.Injective (p i))
    (hAp : ∀ i t, p i t ∈ frontier A) (hBp : ∀ i t, p i t ∈ frontier B)
    (hsep : Function.Injective (fun i => connectedComponentIn (A ∩ B) (p i 0)))
    (hcover : ∀ x ∈ A ∩ B, ¬ (connectedComponentIn (A ∩ B) x).Subsingleton →
      ∃ i, range (p i) ⊆ connectedComponentIn (A ∩ B) x) :
    (nonSingletonComponents (A ∩ B)).encard = (n : ℕ∞) := by
  apply encard_nonSingletonComponents_eq_of_connected_witnesses (A ∩ B) n
    (fun i => range (p i)) (fun i => p i 0)
  · exact fun _ => ⟨0, rfl⟩
  · exact fun i => isPreconnected_range (p i).continuous
  · intro i x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨hA.frontier_subset (hAp i t), hB.frontier_subset (hBp i t)⟩
  · intro i hs
    have : (0 : unitInterval) = 1 := hp i (hs ⟨0, rfl⟩ ⟨1, rfl⟩)
    exact zero_ne_one this
  · exact hsep
  · exact hcover

end LatticeProb
