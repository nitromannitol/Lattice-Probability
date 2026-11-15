import LatticeProb.Prob.CellConfigLabelReversePathLaw

/-! # Observables of labelled cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigLabelTransition

/-- An almost-everywhere measurable observable of a cell walk has the same law
when evaluated on a decoded labelled walk. The configuration is fixed. -/
theorem pathKernel_map_observable_of_leftInverse
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    {E : Type*} [MeasurableSpace E] (F : (ℕ → H.1.cells) → E)
    (hF : AEMeasurable F (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v))) :
    (pathKernel (H, v.val)).map (fun p => F (fun j => decode (p j))) =
      (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v)).map F := by
  have hD : Measurable (fun p : ℕ → ℕ => fun j => decode (p j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable decode).comp (measurable_pi_apply j))
  have hF' : AEMeasurable F ((pathKernel (H, v.val)).map (fun p j => decode (p j))) := by
    rw [pathKernel_map_cell_of_leftInverse H v decode hdecode]
    exact hF
  change (pathKernel (H, v.val)).map (F ∘ fun p j => decode (p j)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hF' hD.aemeasurable,
    pathKernel_map_cell_of_leftInverse H v decode hdecode]

/-- The same identity for the holding-time interpolated cell walk, whenever
that interpolation is almost-everywhere measurable under the cell-walk law. -/
theorem pathKernel_map_interpolatedWalk_of_leftInverse
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    (p : H.1.cells → Plane) (ε : ℝ≥0)
    (hp : AEMeasurable (H.1.interpolatedWalk p ε)
      (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v))) :
    (pathKernel (H, v.val)).map (fun ω => H.1.interpolatedWalk p ε (fun j => decode (ω j))) =
      (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v)).map
        (H.1.interpolatedWalk p ε) :=
  pathKernel_map_observable_of_leftInverse H v decode hdecode _ hp

end LatticeProb.CellConfigLabelTransition
