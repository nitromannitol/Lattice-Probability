import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.Environment.CanonicalSimilarityMeasurable

/-! # Measurability of codes of enumerated cell configurations -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
variable (H : Ω → CellConfig) (C : ι → Ω → Cell)
variable (hvalid : ∀ ω, (H ω).IsCellConfiguration)
variable (hcover : ∀ ω, (H ω).cells = Set.range (fun i => C i ω))
variable (hC : ∀ i, Measurable (C i))

omit [Countable ι] in
include hC in
/-- A fixed enumerated cell carries a given least rational interior label measurably. -/
theorem measurableSet_enumeratedCell_label (i : ι) (n : ℕ) :
    MeasurableSet {ω | Code.LeastInteriorLabel (C i ω) n} := by
  have hh (j : ℕ) : MeasurableSet
      {ω | Code.rationalPoint j ∈ interior (C i ω : Set Plane)} :=
    (hC i) (CanonicalSimilarity.measurableSet_interiorPoint _)
  have heq : {ω | Code.LeastInteriorLabel (C i ω) n} =
      ({ω | Code.rationalPoint n ∈ interior (C i ω : Set Plane)} ∩
        ⋂ j : ℕ, {ω | j < n → Code.rationalPoint j ∉ interior (C i ω : Set Plane)}) := by
    ext ω
    simp [Code.LeastInteriorLabel]
  rw [heq]
  refine (hh n).inter (MeasurableSet.iInter fun j => ?_)
  by_cases hj : j < n
  · convert (hh j).compl using 1
    ext ω
    simp [hj]
  · simp [hj]

include C hvalid hcover hC in
/-- Canonical slots are measurable from a measurable countable enumeration of the cells. -/
theorem measurable_enumeratedCell_slot (n : ℕ) :
    Measurable (fun ω => (H ω).slot n) := by
  classical
  refine CanonicalSimilarity.measurable_of_countable_pieces
    (S := fun i : ι => {ω | Code.LeastInteriorLabel (C i ω) n})
    (g := fun i ω => some (C i ω)) (c := none) ?_ ?_ ?_ ?_
  · exact fun i => measurableSet_enumeratedCell_label C hC i n
  · exact fun i => CanonicalSimilarity.measurable_someCell.comp (hC i)
  · intro i ω hi
    apply (CellConfig.slot_eq_some_iff (hvalid ω)).2
    exact ⟨by rw [hcover ω]; exact ⟨i, rfl⟩, hi⟩
  · intro ω hnone
    apply (CellConfig.slot_eq_none_iff (hvalid ω)).2
    intro K hK hlabel
    rw [hcover ω] at hK
    obtain ⟨i, rfl⟩ := hK
    exact hnone i hlabel

include hvalid hcover hC in
/-- The coded conductances are measurable when the enumerated conductances are. -/
theorem measurable_enumeratedCell_codeCond
    (hc : ∀ i j, Measurable fun ω => (H ω).c (C i ω) (C j ω)) (n m : ℕ) :
    Measurable (fun ω => (H ω).codeCond n m) := by
  classical
  refine CanonicalSimilarity.measurable_of_countable_pieces
    (S := fun p : ι × ι => {ω | Code.LeastInteriorLabel (C p.1 ω) n ∧
      Code.LeastInteriorLabel (C p.2 ω) m})
    (g := fun p ω => (H ω).c (C p.1 ω) (C p.2 ω)) (c := 0) ?_ ?_ ?_ ?_
  · intro p
    exact (measurableSet_enumeratedCell_label C hC p.1 n).inter
      (measurableSet_enumeratedCell_label C hC p.2 m)
  · intro p
    exact hc p.1 p.2
  · intro p ω hp
    have hn : (H ω).slot n = some (C p.1 ω) :=
      (CellConfig.slot_eq_some_iff (hvalid ω)).2
        ⟨by rw [hcover ω]; exact ⟨p.1, rfl⟩, hp.1⟩
    have hm : (H ω).slot m = some (C p.2 ω) :=
      (CellConfig.slot_eq_some_iff (hvalid ω)).2
        ⟨by rw [hcover ω]; exact ⟨p.2, rfl⟩, hp.2⟩
    simp [CellConfig.codeCond, hn, hm]
  · intro ω hnone
    cases hn : (H ω).slot n with
    | none => simp [CellConfig.codeCond, hn]
    | some K =>
      cases hm : (H ω).slot m with
      | none => simp [CellConfig.codeCond, hn, hm]
      | some L =>
        obtain ⟨hK, hKn⟩ := (CellConfig.slot_eq_some_iff (hvalid ω)).1 hn
        obtain ⟨hL, hLm⟩ := (CellConfig.slot_eq_some_iff (hvalid ω)).1 hm
        rw [hcover ω] at hK hL
        obtain ⟨i, rfl⟩ := hK
        obtain ⟨j, rfl⟩ := hL
        exact (hnone (i, j) ⟨hKn, hLm⟩).elim

include hvalid hcover hC in
/-- The complete labelled code is measurable for a measurable cell enumeration. -/
theorem measurable_enumeratedCell_code
    (hc : ∀ i j, Measurable fun ω => (H ω).c (C i ω) (C j ω)) :
    Measurable (fun ω => (H ω).code) := by
  exact (Measurable.of_eval fun n => measurable_enumeratedCell_slot H C hvalid hcover hC n).prodMk
    (Measurable.of_eval fun n => Measurable.of_eval fun m =>
      measurable_enumeratedCell_codeCond H C hvalid hcover hC hc n m)

end LatticeProb
