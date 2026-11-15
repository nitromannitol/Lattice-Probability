import LatticeProb.LQG.ShiftedEdgeDilation
import LatticeProb.LQG.ShiftedMeshVertexWalkLaw

/-! # Time dilation of shifted mesh walk laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic

namespace LatticeProb

/-- Time dilation preserves the totalized coded walk law on corresponding grids. -/
theorem shiftedMeshCodedWalkLaw_time_dilation (w w' : MatedCRT.Path2) (b d θ : ℝ)
    (x : ℤ) (hw : ∀ t, w' t = w (b * t)) :
    shiftedMeshCodedWalkLaw ((w', d, θ), x) =
      shiftedMeshCodedWalkLaw ((w, b * d, θ), x) := by
  have hp := shiftedMeshPath_time_dilation w w' b d θ hw
  unfold shiftedMeshCodedWalkLaw
  dsimp only
  rw [hp]

/-- Time dilation preserves the corresponding totalized vertex walk laws. -/
theorem shiftedMeshVertexWalkKernel_time_dilation (w w' : MatedCRT.Path2) (b d θ : ℝ)
    (x : ℤ) (hw : ∀ t, w' t = w (b * t)) :
    shiftedMeshVertexWalkKernel ((w', d, θ), x) =
      shiftedMeshVertexWalkKernel ((w, b * d, θ), x) := by
  rw [shiftedMeshVertexWalkKernel, Kernel.map_apply _ measurable_meshGridVertexPath,
    Kernel.map_apply _ measurable_meshGridVertexPath]
  change Measure.map meshGridVertexPath (shiftedMeshCodedWalkLaw ((w', d, θ), x)) =
    Measure.map meshGridVertexPath (shiftedMeshCodedWalkLaw ((w, b * d, θ), x))
  rw [shiftedMeshCodedWalkLaw_time_dilation w w' b d θ x hw]

end LatticeProb
