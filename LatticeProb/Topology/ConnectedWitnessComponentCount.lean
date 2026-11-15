import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Set.Card

/-! # Counting components with connected witnesses -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- Connected nontrivial witnesses count the nontrivial components when each such
component contains a witness and distinct witnesses lie in distinct components. -/
theorem ncard_nonSingletonComponents_eq_card_witnesses
    {X ι : Type*} [TopologicalSpace X] (S : Set X) (A : ι → Set X) (p : ι → X)
    (hp : ∀ i, p i ∈ A i) (hconn : ∀ i, IsPreconnected (A i))
    (hsub : ∀ i, A i ⊆ S) (hnontriv : ∀ i, ¬ (A i).Subsingleton)
    (hsep : Function.Injective (fun i => connectedComponentIn S (p i)))
    (hcover : ∀ x ∈ S, ¬ (connectedComponentIn S x).Subsingleton →
      ∃ i, A i ⊆ connectedComponentIn S x) :
    {C ∈ connectedComponentIn S '' S | ¬ C.Subsingleton}.ncard = Nat.card ι := by
  have heq : {C ∈ connectedComponentIn S '' S | ¬ C.Subsingleton} =
      range (fun i => connectedComponentIn S (p i)) := by
    ext C
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      obtain ⟨i, hi⟩ := hcover x hx hn
      exact ⟨i, (connectedComponentIn_eq (hi (hp i))).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨⟨p i, hsub i (hp i), rfl⟩, ?_⟩
      intro hs
      apply hnontriv i
      intro a ha b hb
      exact hs ((hconn i).subset_connectedComponentIn (hp i) (hsub i) ha)
        ((hconn i).subset_connectedComponentIn (hp i) (hsub i) hb)
  rw [heq, Set.ncard_range_of_injective hsep]

end LatticeProb
