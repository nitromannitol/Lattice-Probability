import LatticeProb.Analysis.ReciprocalFloorMesh

/-! # Limit of reciprocal floor meshes -/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- The reciprocal floor mesh tends to zero as the positive scale tends to zero. -/
theorem tendsto_reciprocal_floor_mesh :
    Tendsto (fun b : ℝ => (⌊b⁻¹⌋₊ : ℝ)⁻¹) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    tendsto_reciprocal_floor_mesh_index

end LatticeProb
