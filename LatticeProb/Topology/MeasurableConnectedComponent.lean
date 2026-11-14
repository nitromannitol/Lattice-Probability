import LatticeProb.Topology.ConnectedBasisChain
import LatticeProb.OpenAI.Probability.CriticalZ3.Basic

/-! # Measurable membership in random open components -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Membership in a component of a random open set is measurable when a countable
connected basis has measurable containment and moving-point membership events. -/
theorem measurableSet_mem_connectedComponentIn
    {Ω X ι : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [Countable ι]
    (B : ι → Set X) (U : Ω → Set X) (x y : Ω → X)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set X), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hU : ∀ ω, IsOpen (U ω))
    (hsub : ∀ i, MeasurableSet {ω | B i ⊆ U ω})
    (hx : ∀ i, MeasurableSet {ω | x ω ∈ B i})
    (hy : ∀ i, MeasurableSet {ω | y ω ∈ B i}) :
    MeasurableSet {ω | y ω ∈ connectedComponentIn (U ω) (x ω)} := by
  let r : Ω → ι → ι → Prop := fun ω a b =>
    B a ⊆ U ω ∧ B b ⊆ U ω ∧ (B a ∩ B b).Nonempty
  have hr (a b : ι) : MeasurableSet {ω | r ω a b} :=
    (hsub a).inter ((hsub b).inter (MeasurableSet.const _))
  have heq : {ω | y ω ∈ connectedComponentIn (U ω) (x ω)} =
      ⋃ i, ⋃ j, ({ω | x ω ∈ B i} ∩ {ω | B i ⊆ U ω} ∩
        {ω | B j ⊆ U ω} ∩ {ω | Relation.ReflTransGen (r ω) i j} ∩
        {ω | y ω ∈ B j}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      have hxU : x ω ∈ U ω := connectedComponentIn_nonempty_iff.mp ⟨y ω, h⟩
      obtain ⟨i, hxi, hiU⟩ := hbasis (U ω) (hU ω) (x ω) hxU
      obtain ⟨j, hjU, hij, hyj⟩ :=
        (mem_connectedComponentIn_iff_basis_chain B hopen hconn hbasis (hU ω) hxi hiU).mp h
      exact ⟨i, j, ⟨⟨⟨⟨hxi, hiU⟩, hjU⟩, hij⟩, hyj⟩⟩
    · rintro ⟨i, j, ⟨⟨⟨⟨hxi, hiU⟩, hjU⟩, hij⟩, hyj⟩⟩
      exact (mem_connectedComponentIn_iff_basis_chain B hopen hconn hbasis (hU ω) hxi hiU).mpr
        ⟨j, hjU, hij, hyj⟩
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    ((((hx i).inter (hsub i)).inter (hsub j)).inter
      (OAI.CriticalZ3.measurableSet_rtg r hr i j)).inter (hy j)

end LatticeProb
