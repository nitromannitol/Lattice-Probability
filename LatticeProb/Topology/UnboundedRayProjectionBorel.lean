import LatticeProb.Topology.UnboundedRayProjection
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Borel projection and separability of local curve classes -/

set_option autoImplicit false

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

variable {d : ℕ}

/-- The local curve quotient is separable. -/
instance instSeparableSpace : TopologicalSpace.SeparableSpace (UnboundedRayCurveSpace d) := by
  have hpath : SecondCountableTopology (Path d) := by infer_instance
  let : SecondCountableTopology (Path d) := hpath
  have hsub : SecondCountableTopology (UnboundedRay d) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Path d) _ _ hpath
  let : SecondCountableTopology (UnboundedRay d) := hsub
  have : TopologicalSpace.SeparableSpace (UnboundedRay d) := by infer_instance
  exact surjective_project.denseRange.separableSpace continuous_project

/-- The projection is measurable for the Borel σ-algebras of the given topologies. -/
theorem measurable_project :
    @Measurable (UnboundedRay d) (UnboundedRayCurveSpace d)
      (borel (UnboundedRay d)) (borel (UnboundedRayCurveSpace d)) project := by
  let : MeasurableSpace (UnboundedRay d) := borel _
  let : BorelSpace (UnboundedRay d) := ⟨rfl⟩
  let : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
  let : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩
  exact continuous_project.measurable

end LatticeProb.UnboundedRayCurveSpace
