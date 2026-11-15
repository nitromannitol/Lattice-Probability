/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Section4BallHarmonicMeasure at commit fdb5cad; selected declarations; the local imports are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LocalRegion
import LatticeProb.Bonanno.BouRabeeGwynne.DiscreteHarmonicMeasure

/-! Spatial exit measures and the closed graph region of a ball. -/

open MeasureTheory ProbabilityTheory
open scoped Classical Topology ENNReal

namespace BouRabeeGwynne.OrthogonalTiling

section SpatialHarmonicMeasure

variable {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))
variable [Fintype (T.closedVertices U)] [MeasurableSpace (T.closedVertices U)]
variable [MeasurableSingletonClass (T.closedVertices U)]

/-- The exit measure of the actual finite conductance walk, in Euclidean space. -/
noncomputable def spatialHarmonicMeasure
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (v : T.closedVertices U) : Measure (Euc d) :=
  ((T.finiteNetwork (T.closedVertices U)).discreteHarmonicMeasure (T.finiteInterior U)
    ((T.finiteNetwork (T.closedVertices U)).totalConductance_pos_of_boundaryAccessible
      (T.finiteInterior U) ha) v).map (fun w : T.closedVertices U => T.pos w)

instance spatialHarmonicMeasure_isProbabilityMeasure
    (ha : (T.finiteNetwork (T.closedVertices U)).BoundaryAccessible (T.finiteInterior U))
    (v : T.closedVertices U) : IsProbabilityMeasure (T.spatialHarmonicMeasure U ha v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_finite
    (fun w : T.closedVertices U => T.pos w)).aemeasurable).mpr inferInstance

end SpatialHarmonicMeasure

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The actual closed graph region of a ball has only a two-mesh overshoot. -/
lemma closedVertices_pos_mem_enlarged_ball {c : Euc d} {r : ℝ}
    (hmesh : T.mesh ≠ ∞) {w : T.V} (hw : w ∈ T.closedVertices (Metric.ball c r)) :
    T.pos w ∈ Metric.closedBall c (r + 2 * T.mesh.toReal) := by
  change dist (T.pos w) c ≤ r + 2 * T.mesh.toReal
  rcases hw with hw | hw
  · exact (Metric.mem_ball.mp hw).le.trans
      (le_add_of_nonneg_right (mul_nonneg zero_le_two ENNReal.toReal_nonneg))
  · obtain ⟨v, hv, hdist⟩ := T.boundaryVertices_near_interior hw hmesh
    calc
      _ ≤ dist (T.pos w) (T.pos v) + dist (T.pos v) c := dist_triangle _ _ _
      _ ≤ 2 * T.mesh.toReal + r := add_le_add hdist (Metric.mem_ball.mp hv).le
      _ = _ := add_comm _ _

end BouRabeeGwynne.OrthogonalTiling
