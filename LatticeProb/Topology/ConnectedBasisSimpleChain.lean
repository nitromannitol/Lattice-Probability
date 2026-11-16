import LatticeProb.Topology.ConnectedBasisChain
import Mathlib.Data.List.Chain

/-! # Duplicate-free chains of connected basis sets -/

set_option autoImplicit false

open Set

namespace LatticeProb

variable {ι : Type*}

/-- **Loop erasure.** If `b` is reachable from `x` by steps of `r` whose targets lie in `s`, and
`x ∈ s`, then there is a nodup `r`-chain in `s` from `x` to `b`. -/
theorem exists_nodup_isChain_of_reflTransGen {r : ι → ι → Prop} {s : Set ι} {x b : ι}
    (h : Relation.ReflTransGen (fun a c => c ∈ s ∧ r a c) x b) (hx : x ∈ s) :
    ∃ l : List ι, (x :: l).Nodup ∧ (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ s) ∧
      (x :: l).getLast (List.cons_ne_nil x l) = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], List.nodup_singleton _, List.isChain_singleton _, by simpa using hx, rfl⟩
  | @head a c hac _ ih =>
    obtain ⟨l, hnd, hch, hs, hl⟩ := ih hac.1
    by_cases ha : a ∈ c :: l
    · obtain ⟨p, q, hpq⟩ := List.append_of_mem ha
      refine ⟨q, ?_, ?_, ?_, ?_⟩
      · rw [hpq] at hnd
        exact hnd.sublist (List.sublist_append_right p (a :: q))
      · rw [hpq] at hch
        exact hch.suffix (List.suffix_append p (a :: q))
      · intro v hv
        exact hs v (hpq ▸ List.mem_append_right p hv)
      · have h1 : (c :: l).getLast? = some b := by
          rw [List.getLast?_eq_some_getLast (List.cons_ne_nil c l), hl]
        rw [hpq, List.getLast?_append] at h1
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a q)] at h1
        simpa using h1
    · refine ⟨c :: l, List.nodup_cons.2 ⟨ha, hnd⟩, List.IsChain.cons_cons hac.2 hch, ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hx
        · exact hs v hv
      · rw [List.getLast_cons (List.cons_ne_nil c l)]
        exact hl

/-- A connected component can be reached by a duplicate-free chain of basis
sets contained in the open set, with consecutive sets intersecting. -/
theorem exists_nodup_basis_chain_of_mem_connectedComponentIn
    {X : Type*} [TopologicalSpace X] (B : ι → Set X)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set X), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    {U : Set X} (hU : IsOpen U) {x y : X} {i : ι} (hxi : x ∈ B i)
    (hiU : B i ⊆ U) (hy : y ∈ connectedComponentIn U x) :
    ∃ l : List ι, (i :: l).Nodup ∧
      (i :: l).IsChain (fun a b => (B a ∩ B b).Nonempty) ∧
      (∀ j ∈ i :: l, B j ⊆ U) ∧
      y ∈ B ((i :: l).getLast (List.cons_ne_nil i l)) := by
  obtain ⟨j, hjU, hreach, hyj⟩ :=
    (mem_connectedComponentIn_iff_basis_chain B hopen hconn hbasis hU hxi hiU).mp hy
  have hreach' : Relation.ReflTransGen
      (fun a b => B b ⊆ U ∧ (B a ∩ B b).Nonempty) i j :=
    Relation.ReflTransGen.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) i j hreach
  obtain ⟨l, hnd, hch, hsub, hlast⟩ :=
    exists_nodup_isChain_of_reflTransGen hreach' hiU
  exact ⟨l, hnd, hch, hsub, hlast ▸ hyj⟩

end LatticeProb
