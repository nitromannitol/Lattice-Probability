import LatticeProb.Prob.CellConfigContainingCell
import LatticeProb.Prob.CellConfigWalkMeasurable
import LatticeProb.MeasureTheory.ExclusiveCellPoint

/-! # Exclusive interior points of cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Function
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigContainingCell

/-- Each cell has an interior point which belongs to no other cell. -/
theorem exists_interior_mem_only (H : GMSSpace) (K : H.1.cells) :
    ∃ z ∈ interior (K.1 : Set Plane),
      ∀ J : H.1.cells, z ∈ (J.1 : Set Plane) → J = K := by
  classical
  let : Countable H.1.cells := CellConfigWalk.countable_cells_of_locallyFinite H.2.locallyFinite
  let C : H.1.cells → Set Plane := fun J => (J.1 : Set Plane) ∩ interior (K.1 : Set Plane)
  have hdisj : Pairwise (AEDisjoint volume on C) := by
    intro I J hIJ
    change volume (C I ∩ C J) = 0
    apply measure_mono_null _
      (H.2.volume_inter I.1 I.2 J.1 J.2 (fun h => hIJ (Subtype.ext h)))
    intro z hz
    exact ⟨hz.1.1, hz.2.1⟩
  have hpos : 0 < volume (C K) := by
    have heq : C K = interior (K.1 : Set Plane) := inter_eq_right.mpr interior_subset
    rw [heq]
    exact isOpen_interior.measure_pos volume (H.2.interior_nonempty K.1 K.2)
  obtain ⟨z, hz, hzonly⟩ := exists_mem_only_of_pairwise_ae_disjoint volume C hdisj K hpos
  refine ⟨z, hz.2, ?_⟩
  intro J hJ
  exact hzonly J ⟨hJ, hz.2⟩

/-- At an exclusive point, the containing-cell selector returns its unique cell. -/
theorem containingCell_eq_of_mem_only (H : GMSSpace) (K : H.1.cells) (z : Plane)
    (h : ∀ J : H.1.cells, z ∈ (J.1 : Set Plane) → J = K) :
    containingCell (H, z) = K.1 := by
  have heq := h ⟨containingCell (H, z), containingCell_mem (H, z)⟩
    (mem_containingCell (H, z))
  exact congrArg Subtype.val heq

end LatticeProb.CellConfigContainingCell
