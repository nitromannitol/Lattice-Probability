import LatticeProb.Prob.CellConfigLabelObservable
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Interpolated walks on recurrent cell configurations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigLabelTransition

/-- On a fixed recurrent configuration with positive holding times, the interpolation
of the decoded labelled walk has the law of the interpolated cell walk. -/
theorem pathKernel_map_interpolatedWalk_of_recurrent
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    (hrec : H.1.Recurrent) (hpos : ∀ K, 0 < H.1.holding K)
    (hpi : 0 < H.1.pi (H.1.cellEquiv H.2 v))
    (p : H.1.cells → Plane) (ε : ℝ≥0) :
    (pathKernel (H, v.val)).map (fun ω => H.1.interpolatedWalk p ε (fun j => decode (ω j))) =
      (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v)).map
        (H.1.interpolatedWalk p ε) := by
  apply pathKernel_map_interpolatedWalk_of_leftInverse H v decode hdecode p ε
  exact CellConfigWalk.aemeasurable_interpolatedWalk_of_recurrent hrec hpos
    (CellConfigSRW.isSRWLaw_walkLaw H.1 H.2 hpi) p ε

/-- The same law identity when every cell has a neighbour. -/
theorem pathKernel_map_interpolatedWalk_of_recurrent_of_forall_exists_adj
    (H : GMSSpace) [Countable H.1.cells]
    (v : Code.Vertex H.1.code) (decode : ℕ → H.1.cells)
    (hdecode : Function.LeftInverse decode (cellLabel H))
    (hrec : H.1.Recurrent) (hadj : ∀ K : H.1.cells, ∃ K' : H.1.cells, H.1.Adj K K')
    (p : H.1.cells → Plane) (ε : ℝ≥0) :
    (pathKernel (H, v.val)).map (fun ω => H.1.interpolatedWalk p ε (fun j => decode (ω j))) =
      (CellConfigSRW.walkLaw H.1 H.2 (H.1.cellEquiv H.2 v)).map
        (H.1.interpolatedWalk p ε) := by
  obtain ⟨K', hK'⟩ := hadj (H.1.cellEquiv H.2 v)
  exact pathKernel_map_interpolatedWalk_of_recurrent H v decode hdecode hrec
    (CellConfigWalk.holding_pos_of_forall_exists_adj H.2 hadj)
    (CellConfigWalk.pi_pos_of_adj H.2 hK') p ε

end LatticeProb.CellConfigLabelTransition
