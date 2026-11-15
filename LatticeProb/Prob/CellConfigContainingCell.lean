import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CellSlotMeasurable

/-! # Measurable selection of a cell containing a point

Canonical rational-interior labels give a jointly measurable selection, including at points
belonging to several cells. -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigContainingCell

/-- The labelled cell contains the point. -/
def containingSet (n : ℕ) : Set (GMSSpace × Plane) :=
  {p | p.1 ∈ labelSet n ∧ p.2 ∈ (interiorCell (Code.rationalPoint n) p.1 : Set Plane)}

theorem measurableSet_containingSet (n : ℕ) : MeasurableSet (containingSet n) :=
  (measurable_fst (measurableSet_labelSet n)).inter
    ((((measurable_interiorCell (Code.rationalPoint n)).comp measurable_fst).prodMk
      measurable_snd) Spatial.measurableSet_cellMem)

theorem exists_containingSet (p : GMSSpace × Plane) : ∃ n, p ∈ containingSet n := by
  obtain ⟨H, z⟩ := p
  have hz : z ∈ ⋃ K ∈ H.1.cells, (K : Set Plane) := by
    rw [H.2.iUnion_eq_univ]
    exact Set.mem_univ _
  obtain ⟨K, hK, hzK⟩ := Set.mem_iUnion₂.mp hz
  let K' : H.1.cells := ⟨K, hK⟩
  let n := CellConfig.label H.2 K'
  have hn : H ∈ labelSet n :=
    ⟨K, hK, CellConfig.leastInteriorLabel_label H.2 K'⟩
  have heq : interiorCell (Code.rationalPoint n) H = K := by
    have hs := slot_eq H n
    rw [show H.1.slot n = some K from CellConfig.slot_label H.2 K'] at hs
    simp only [hn, ↓reduceIte, Option.some_inj] at hs
    exact hs.symm
  exact ⟨n, hn, by rw [heq]; exact hzK⟩

/-- The least canonical label of a cell containing the point. -/
noncomputable def containingLabel (p : GMSSpace × Plane) : ℕ := by
  classical
  exact Nat.find (exists_containingSet p)

theorem measurable_containingLabel : Measurable containingLabel := by
  classical
  exact measurable_find exists_containingSet measurableSet_containingSet

theorem mem_containingSet_containingLabel (p : GMSSpace × Plane) :
    p ∈ containingSet (containingLabel p) := by
  classical
  exact Nat.find_spec (exists_containingSet p)

/-- A canonical containing cell, as an ambient compact cell. -/
noncomputable def containingCell (p : GMSSpace × Plane) : Cell :=
  interiorCell (Code.rationalPoint (containingLabel p)) p.1

set_option maxHeartbeats 400000 in
theorem measurable_containingCell : Measurable containingCell := by
  have h : Measurable (fun q : ℕ × (GMSSpace × Plane) =>
      interiorCell (Code.rationalPoint q.1) q.2.1) :=
    measurable_from_prod_countable_right (fun n =>
      (measurable_interiorCell (Code.rationalPoint n)).comp measurable_fst)
  have hp : Measurable (fun p : GMSSpace × Plane => (containingLabel p, p)) :=
    measurable_containingLabel.prodMk measurable_id
  change Measurable ((fun q : ℕ × (GMSSpace × Plane) =>
    interiorCell (Code.rationalPoint q.1) q.2.1) ∘
      (fun p : GMSSpace × Plane => (containingLabel p, p)))
  exact h.comp hp

theorem containingCell_mem (p : GMSSpace × Plane) : containingCell p ∈ p.1.1.cells :=
  (interiorCell_spec (labelSet_subset _ (mem_containingSet_containingLabel p).1)).1

theorem mem_containingCell (p : GMSSpace × Plane) : p.2 ∈ (containingCell p : Set Plane) :=
  (mem_containingSet_containingLabel p).2

end LatticeProb.CellConfigContainingCell
