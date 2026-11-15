import LatticeProb.Topology.CompactCommonPoint
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-! # Measurable containment of compact intersections -/

set_option autoImplicit false

open Set TopologicalSpace MeasureTheory

namespace LatticeProb.Topology

/-- For four varying nonempty compact sets, containment of the intersection of
    the first two in the union of the last two is a Borel condition. -/
theorem measurableSet_inter_subset_union_nonemptyCompacts
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)] :
    MeasurableSet {p : (NonemptyCompacts X × NonemptyCompacts X) ×
        (NonemptyCompacts X × NonemptyCompacts X) |
      (p.1.1 : Set X) ∩ p.1.2 ⊆ (p.2.1 : Set X) ∪ p.2.2} := by
  let S : Set (Set X) := {s | s ∈ countableBasis X ∧ IsCompact (closure s)}
  have : Countable S := ((countable_countableBasis X).mono (by
    intro s hs
    exact hs.1)).to_subtype
  let E : S → Set ((NonemptyCompacts X × NonemptyCompacts X) ×
      (NonemptyCompacts X × NonemptyCompacts X)) := fun s => {p |
    (∃ x ∈ closure s.1, x ∈ (p.1.1 : Set X) ∧ x ∈ (p.1.2 : Set X)) ∧
    (p.2.1 : Set X) ⊆ (closure s.1)ᶜ ∧
    (p.2.2 : Set X) ⊆ (closure s.1)ᶜ}
  have hE : ∀ s, MeasurableSet (E s) := by
    intro s
    have h₁ : MeasurableSet {p : (NonemptyCompacts X × NonemptyCompacts X) ×
        (NonemptyCompacts X × NonemptyCompacts X) |
        ∃ x ∈ closure s.1, x ∈ (p.1.1 : Set X) ∧ x ∈ (p.1.2 : Set X)} :=
      (isClosed_exists_mem_inter_compact s.2.2).measurableSet.preimage measurable_fst
    have h₂ := (NonemptyCompacts.isOpen_subsets_of_isOpen
      (isClosed_closure.isOpen_compl : IsOpen (closure s.1)ᶜ)).measurableSet
    exact h₁.inter ((h₂.preimage (measurable_fst.comp measurable_snd)).inter
      (h₂.preimage (measurable_snd.comp measurable_snd)))
  have heq : {p : (NonemptyCompacts X × NonemptyCompacts X) ×
      (NonemptyCompacts X × NonemptyCompacts X) |
      (p.1.1 : Set X) ∩ p.1.2 ⊆ (p.2.1 : Set X) ∪ p.2.2}ᶜ = ⋃ s : S, E s := by
    ext p
    simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨x, hx, hxout⟩ := not_subset.mp h
      have hopen : IsOpen (((p.2.1 : Set X) ∪ p.2.2)ᶜ) :=
        (p.2.1.isCompact.isClosed.union p.2.2.isCompact.isClosed).isOpen_compl
      obtain ⟨H, hH, hxH, hHU⟩ := exists_compact_subset hopen hxout
      obtain ⟨s, hs, hxs, hsH⟩ :=
        (isBasis_countableBasis X).exists_subset_of_mem_open hxH isOpen_interior
      have hscl : closure s ⊆ H := closure_minimal (hsH.trans interior_subset) hH.isClosed
      have hc : IsCompact (closure s) := hH.of_isClosed_subset isClosed_closure hscl
      refine ⟨⟨s, hs, hc⟩, ⟨⟨x, subset_closure hxs, hx.1, hx.2⟩, ?_, ?_⟩⟩
      · intro y hy hycl
        exact hHU (hscl hycl) (Or.inl hy)
      · intro y hy hycl
        exact hHU (hscl hycl) (Or.inr hy)
    · rintro ⟨s, ⟨⟨x, hxF, hxA, hxB⟩, hK, hL⟩⟩ hsub
      rcases hsub ⟨hxA, hxB⟩ with hxK | hxL
      · exact hK hxK hxF
      · exact hL hxL hxF
  have hh : MeasurableSet {p : (NonemptyCompacts X × NonemptyCompacts X) ×
      (NonemptyCompacts X × NonemptyCompacts X) |
      (p.1.1 : Set X) ∩ p.1.2 ⊆ (p.2.1 : Set X) ∪ p.2.2}ᶜ := by
    rw [heq]
    exact MeasurableSet.iUnion hE
  simpa only [compl_compl] using hh.compl

end LatticeProb.Topology
