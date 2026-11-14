import LatticeProb.LQG.ShiftedMeshEdgeCode
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalkWeights

/-! # Measurable walk weights on a shifted mesh -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling

namespace LatticeProb

/-- Fixed coded walk-prefix weights are measurable in the shifted time grid. -/
theorem measurable_shiftedMeshCodePrefixWeight (x : ℤ)
    (s : ℕ → MeshGridStateCode) (n : ℕ) :
    Measurable (fun p : MatedCRT.Path2 × ℝ × ℝ =>
      meshGridCodePrefixWeight 1 x s n (shiftedMeshPath p.1 p.2.1 p.2.2)) :=
  (measurable_meshGridCodePrefixWeight 1 x s n).comp continuous_shiftedMeshPath.measurable

/-- The starting integer can vary measurably along with the shifted time grid. -/
theorem measurable_shiftedMeshCodePrefixWeight_start
    (s : ℕ → MeshGridStateCode) (n : ℕ) :
    Measurable (fun p : (MatedCRT.Path2 × ℝ × ℝ) × ℤ =>
      meshGridCodePrefixWeight 1 p.2 s n
        (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)) :=
  measurable_from_prod_countable_left (fun x => measurable_shiftedMeshCodePrefixWeight x s n)

end LatticeProb
