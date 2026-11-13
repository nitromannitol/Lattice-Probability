/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.MeasureTheory.HausdorffPlane at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# One-dimensional Hausdorff-null subsets of the plane are Lebesgue-null

The singular-set manuscript assumes `H¹(Ssing) = 0` for the uncovered set (Definition 1.1(ii)).
Every argument that only needs "the cells cover Lebesgue-almost every point" consumes that
hypothesis through the implication proved here.

The proof is the standard dimension comparison: `μH[1] s = 0` forces `dimH s ≤ 1 < 2`, so
`μH[2] s = 0`; and on `EuclideanSpace ℝ (Fin 2)` the measure `μH[2]` is an additive Haar measure
(`Mathlib/Geometry/Euclidean/Volume/Measure.lean`), so `volume` is a scalar multiple of it by Haar
uniqueness.

No measurability of `s` is required: both steps are statements about outer measures.
-/

set_option autoImplicit false

open MeasureTheory Measure Set
open scoped NNReal ENNReal

namespace ReflectedGMS

/-- On the plane, `volume` is a scalar multiple of the two-dimensional Hausdorff measure. -/
theorem volume_plane_eq_smul_hausdorffMeasure :
    (volume : Measure Plane)
      = addHaarScalarFactor (volume : Measure Plane) (μH[(2 : ℕ)]) • (μH[(2 : ℕ)]) :=
  isAddLeftInvariant_eq_smul (volume : Measure Plane) (μH[(2 : ℕ)])

/-- A set of vanishing two-dimensional Hausdorff measure is Lebesgue-null in the plane. -/
theorem volume_eq_zero_of_hausdorffMeasure_two {s : Set Plane} (h : μH[(2 : ℝ)] s = 0) :
    volume s = 0 := by
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have h' : (μH[(2 : ℕ)] : Measure Plane) s = 0 := by rw [hcast]; exact h
  rw [volume_plane_eq_smul_hausdorffMeasure, Measure.smul_apply, h', smul_zero]

/-- **`H¹`-null implies Lebesgue-null in the plane.** This is the only consequence of the
manuscript's `H¹(Ssing) = 0` hypothesis that the covering arguments need. -/
theorem volume_eq_zero_of_hausdorffMeasure_one {s : Set Plane} (h : μH[(1 : ℝ)] s = 0) :
    volume s = 0 := by
  have hne : μH[((1 : ℝ≥0) : ℝ)] s ≠ ⊤ := by
    have hcast : ((1 : ℝ≥0) : ℝ) = (1 : ℝ) := by norm_num
    rw [hcast, h]
    exact ENNReal.zero_ne_top
  have hdim : dimH s ≤ ((1 : ℝ≥0) : ℝ≥0∞) := dimH_le_of_hausdorffMeasure_ne_top hne
  have hlt : dimH s < ((2 : ℝ≥0) : ℝ≥0∞) := by
    refine lt_of_le_of_lt hdim ?_
    exact_mod_cast (by norm_num : (1 : ℝ≥0) < 2)
  have h2 : μH[((2 : ℝ≥0) : ℝ)] s = 0 := hausdorffMeasure_of_dimH_lt hlt
  refine volume_eq_zero_of_hausdorffMeasure_two ?_
  have hcast : ((2 : ℝ≥0) : ℝ) = (2 : ℝ) := by norm_num
  rw [← hcast]; exact h2

end ReflectedGMS
