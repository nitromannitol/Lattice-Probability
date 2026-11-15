import LatticeProb.Prob.CellConfigLabelCellPathLaw

/-! # Recovering cell walks from labelled trajectories -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- Any left inverse of the cell labels recovers the whole cell-walk law. -/
theorem pathKernel_map_cell_of_leftInverse (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H)) :
    (pathKernel (H, v.val)).map (fun p j => decode (p j)) =
      CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v) := by
  have hlabel : Measurable (fun p : ℕ → H.1.cells => fun j => cellLabel H (p j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable (cellLabel H)).comp (measurable_pi_apply j))
  have hdecode' : Measurable (fun p : ℕ → ℕ => fun j => decode (p j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable decode).comp (measurable_pi_apply j))
  rw [← cellWalk_map_label H v, Measure.map_map hdecode' hlabel]
  have heq : (fun p : ℕ → H.1.cells => fun j => decode (cellLabel H (p j))) = id := by
    funext p j
    exact hdecode (p j)
  change Measure.map (fun p : ℕ → H.1.cells => fun j => decode (cellLabel H (p j))) _ = _
  rw [heq, Measure.map_id]

/-- An occupied label supplies a fallback for decoding all natural labels. -/
theorem exists_cellLabel_leftInverse (H : GMSSpace) (v : Code.Vertex H.1.code) :
    ∃ decode : ℕ → H.1.cells, Function.LeftInverse decode (cellLabel H) := by
  classical
  let decode : ℕ → H.1.cells := fun n =>
    if h : (H.1.slot n).isSome = true then H.1.cellEquiv H.2 ⟨n, h⟩
    else H.1.cellEquiv H.2 v
  refine ⟨decode, ?_⟩
  intro K
  let w := (H.1.cellEquiv H.2).symm K
  have hw : (H.1.slot (cellLabel H K)).isSome = true := w.property
  simp only [decode, hw, ↓reduceDIte]
  change H.1.cellEquiv H.2 w = K
  exact (H.1.cellEquiv H.2).apply_symm_apply K

end LatticeProb.CellConfigLabelTransition
