import LatticeProb.Prob.CellConfigLabelObservable
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Measurability of interpolated labelled walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigLabelTransition

/-- For a fixed recurrent configuration, interpolating the decoded labelled walk is
almost-everywhere measurable under the labelled path law. -/
theorem aemeasurable_decoded_interpolatedWalk_of_recurrent
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    (hrec : H.1.Recurrent) (hpos : ∀ K, 0 < H.1.holding K)
    (hpi : 0 < H.1.pi (H.1.cellEquiv H.2 v))
    (p : H.1.cells → Plane) (ε : ℝ≥0) :
    AEMeasurable (fun ω => H.1.interpolatedWalk p ε (fun j => decode (ω j)))
      (pathKernel (H, v.val)) := by
  have hD : Measurable (fun ω : ℕ → ℕ => fun j => decode (ω j)) :=
    Measurable.of_eval (fun j => (measurable_of_countable decode).comp (measurable_pi_apply j))
  have hF : AEMeasurable (H.1.interpolatedWalk p ε)
      ((pathKernel (H, v.val)).map (fun ω j => decode (ω j))) := by
    rw [pathKernel_map_cell_of_leftInverse H v decode hdecode]
    exact CellConfigWalk.aemeasurable_interpolatedWalk_of_recurrent hrec hpos
      (CellConfigSRW.isSRWLaw_walkLaw H.1 H.2 hpi) p ε
  exact hF.comp_measurable hD

/-- If every cell has a neighbour, the required holding times and starting
conductance are positive. -/
theorem aemeasurable_decoded_interpolatedWalk_of_recurrent_of_forall_exists_adj
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    (hrec : H.1.Recurrent) (hadj : ∀ K : H.1.cells, ∃ K' : H.1.cells, H.1.Adj K K')
    (p : H.1.cells → Plane) (ε : ℝ≥0) :
    AEMeasurable (fun ω => H.1.interpolatedWalk p ε (fun j => decode (ω j)))
      (pathKernel (H, v.val)) := by
  obtain ⟨K', hK'⟩ := hadj (H.1.cellEquiv H.2 v)
  exact aemeasurable_decoded_interpolatedWalk_of_recurrent H v decode hdecode hrec
    (CellConfigWalk.holding_pos_of_forall_exists_adj H.2 hadj)
    (CellConfigWalk.pi_pos_of_adj H.2 hK') p ε

end LatticeProb.CellConfigLabelTransition
