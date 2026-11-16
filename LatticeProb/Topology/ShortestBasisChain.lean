import LatticeProb.Topology.ConnectedBasisSimpleChain

/-! # Shortest admissible chains of basis sets -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Among duplicate-free directed chains with fixed endpoints and vertices in `s`,
there is one of minimal length. -/
theorem exists_shortest_nodup_isChain_of_reflTransGen {ι : Type*}
    {r : ι → ι → Prop} {s : Set ι} {x b : ι}
    (h : Relation.ReflTransGen (fun a c => c ∈ s ∧ r a c) x b) (hx : x ∈ s) :
    ∃ l : List ι, (x :: l).Nodup ∧ (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ s) ∧
      (x :: l).getLast (List.cons_ne_nil x l) = b ∧
      ∀ k : List ι, (x :: k).Nodup → (x :: k).IsChain r →
        (∀ v ∈ x :: k, v ∈ s) → (x :: k).getLast (List.cons_ne_nil x k) = b →
        l.length ≤ k.length := by
  classical
  let P : ℕ → Prop := fun n => ∃ l : List ι, l.length = n ∧ (x :: l).Nodup ∧
    (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ s) ∧
    (x :: l).getLast (List.cons_ne_nil x l) = b
  have hex : ∃ n, P n := by
    obtain ⟨l, hnd, hch, hs, hl⟩ := exists_nodup_isChain_of_reflTransGen h hx
    exact ⟨l.length, l, rfl, hnd, hch, hs, hl⟩
  obtain ⟨l, hlen, hnd, hch, hs, hl⟩ := Nat.find_spec hex
  refine ⟨l, hnd, hch, hs, hl, ?_⟩
  intro k hknd hkch hks hkl
  rw [hlen]
  exact Nat.find_min' hex ⟨k, rfl, hknd, hkch, hks, hkl⟩

/-- In an open connected component, an admissible duplicate-free chain of basis
sets can be chosen shortest among those with the same terminal basis set. -/
theorem exists_shortest_basis_chain_of_mem_connectedComponentIn
    {X ι : Type*} [TopologicalSpace X] (B : ι → Set X)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set X), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    {U : Set X} (hU : IsOpen U) {x y : X} {i : ι} (hxi : x ∈ B i)
    (hiU : B i ⊆ U) (hy : y ∈ connectedComponentIn U x) :
    ∃ (j : ι) (l : List ι), (i :: l).Nodup ∧
      (i :: l).IsChain (fun a b => (B a ∩ B b).Nonempty) ∧
      (∀ v ∈ i :: l, B v ⊆ U) ∧
      (i :: l).getLast (List.cons_ne_nil i l) = j ∧ y ∈ B j ∧
      ∀ k : List ι, (i :: k).Nodup →
        (i :: k).IsChain (fun a b => (B a ∩ B b).Nonempty) →
        (∀ v ∈ i :: k, B v ⊆ U) →
        (i :: k).getLast (List.cons_ne_nil i k) = j → l.length ≤ k.length := by
  obtain ⟨j, hjU, hreach, hyj⟩ :=
    (mem_connectedComponentIn_iff_basis_chain B hopen hconn hbasis hU hxi hiU).mp hy
  have hreach' : Relation.ReflTransGen
      (fun a b => B b ⊆ U ∧ (B a ∩ B b).Nonempty) i j :=
    Relation.ReflTransGen.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) i j hreach
  obtain ⟨l, hnd, hch, hs, hl, hmin⟩ :=
    exists_shortest_nodup_isChain_of_reflTransGen hreach' hiU
  exact ⟨j, l, hnd, hch, hs, hl, hyj, hmin⟩

end LatticeProb
