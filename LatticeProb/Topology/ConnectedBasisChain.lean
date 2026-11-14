import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Closure

/-! # Connected components and chains of basis sets -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An open connected component is the union of the basis sets reached by finite
chains of intersecting preconnected basis sets contained in the open set. -/
theorem mem_connectedComponentIn_iff_basis_chain
    {X ι : Type*} [TopologicalSpace X] (B : ι → Set X)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set X), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    {U : Set X} (hU : IsOpen U) {x y : X} {i : ι} (hxi : x ∈ B i)
    (hiU : B i ⊆ U) :
    y ∈ connectedComponentIn U x ↔
      ∃ j, B j ⊆ U ∧ Relation.ReflTransGen
        (fun a b => B a ⊆ U ∧ B b ⊆ U ∧ (B a ∩ B b).Nonempty) i j ∧ y ∈ B j := by
  let r : ι → ι → Prop := fun a b =>
    B a ⊆ U ∧ B b ⊆ U ∧ (B a ∩ B b).Nonempty
  let R : Set X := ⋃ j, ⋃ (_ : B j ⊆ U), ⋃ (_ : Relation.ReflTransGen r i j), B j
  have hRopen : IsOpen R := by
    exact isOpen_iUnion fun j => isOpen_iUnion fun _ => isOpen_iUnion fun _ => hopen j
  have hxR : x ∈ R := by
    simp only [R, mem_iUnion]
    exact ⟨i, hiU, Relation.ReflTransGen.refl, hxi⟩
  have hreach : ∀ j, Relation.ReflTransGen r i j →
      B j ⊆ U → B j ⊆ connectedComponentIn U x := by
    intro j hj
    induction hj with
    | refl =>
      intro hsub
      exact (hconn i).subset_connectedComponentIn hxi hsub
    | @tail a b ha hab ih =>
      intro hbU
      obtain ⟨z, hza, hzb⟩ := hab.2.2
      have hzC : z ∈ connectedComponentIn U x := ih hab.1 hza
      have hsub : B b ⊆ connectedComponentIn U z :=
        (hconn b).subset_connectedComponentIn hzb hbU
      rw [← connectedComponentIn_eq hzC] at hsub
      exact hsub
  have hRC : R ⊆ connectedComponentIn U x := by
    intro z hz
    simp only [R, mem_iUnion] at hz
    obtain ⟨j, hjU, hj, hzj⟩ := hz
    exact hreach j hj hjU hzj
  have hclosure : closure R ∩ connectedComponentIn U x ⊆ R := by
    intro z hz
    have hzU : z ∈ U := connectedComponentIn_subset U x hz.2
    obtain ⟨k, hzk, hkU⟩ := hbasis U hU z hzU
    obtain ⟨w, hwk, hwR⟩ := (mem_closure_iff.mp hz.1) (B k) (hopen k) hzk
    simp only [R, mem_iUnion] at hwR
    obtain ⟨j, hjU, hj, hwj⟩ := hwR
    have hjk : r j k := ⟨hjU, hkU, w, hwj, hwk⟩
    simp only [R, mem_iUnion]
    exact ⟨k, hkU, hj.tail hjk, hzk⟩
  have hCR : connectedComponentIn U x ⊆ R :=
    isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hRopen
      ⟨x, mem_connectedComponentIn (hiU hxi), hxR⟩ hclosure
  constructor
  · intro hy
    have : y ∈ R := hCR hy
    simp only [R, mem_iUnion] at this
    obtain ⟨j, hjU, hj, hyj⟩ := this
    exact ⟨j, hjU, hj, hyj⟩
  · rintro ⟨j, hjU, hj, hyj⟩
    apply hRC
    simp only [R, mem_iUnion]
    exact ⟨j, hjU, hj, hyj⟩

end LatticeProb
