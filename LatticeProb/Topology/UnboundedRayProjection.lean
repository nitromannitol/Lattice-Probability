import LatticeProb.Topology.UnboundedRayProjectionLimit
import LatticeProb.Prob.PathSpaceDUnif

/-! # Continuity of the projection to local curve classes -/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand UnboundedRayLocalDistance

variable {d : ℕ}

/-- The projection from locally uniform paths to local curve classes is continuous. -/
theorem continuous_project : Continuous (project (d := d)) := by
  have hfc : FirstCountableTopology (Path d) := by
    let : MetricSpace (Path d) := dUnifMetricSpace
    infer_instance
  let : FirstCountableTopology (Path d) := hfc
  have hsub : FirstCountableTopology (UnboundedRay d) := by
    exact @TopologicalSpace.Subtype.firstCountableTopology (Path d) _ _ hfc
  let : FirstCountableTopology (UnboundedRay d) := hsub
  rw [continuous_iff_continuousAt]
  intro f
  apply tendsto_iff_edist_tendsto_0.2
  have h := tendsto_localEDist (tendsto_id : Tendsto id (𝓝 f) (𝓝 f))
  simp only [id_eq] at h
  simp_rw [edist_project]
  exact h

end LatticeProb.UnboundedRayCurveSpace
