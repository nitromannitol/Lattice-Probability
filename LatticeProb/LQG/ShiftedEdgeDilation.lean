import LatticeProb.LQG.ShiftedMeshEdgeCode

/-! # Time dilation of shifted boundary paths and edge codes -/

set_option autoImplicit false

open MatedCRTHarmonic

namespace LatticeProb

/-- Time dilation of a boundary path multiplies the shifted mesh by the same factor. -/
theorem shiftedMeshPath_time_dilation (w w' : MatedCRT.Path2) (b d θ : ℝ)
    (hw : ∀ t, w' t = w (b * t)) :
    shiftedMeshPath w' d θ = shiftedMeshPath w (b * d) θ := by
  apply ContinuousMap.ext
  intro t
  simp only [shiftedMeshPath_apply, hw, mul_assoc]

/-- Time dilation preserves every side-labelled edge of the corresponding shifted grid. -/
theorem shiftedMeshEdgeCode_time_dilation (w w' : MatedCRT.Path2) (b d θ : ℝ)
    (hw : ∀ t, w' t = w (b * t)) :
    shiftedMeshEdgeCode w' d θ = shiftedMeshEdgeCode w (b * d) θ := by
  unfold shiftedMeshEdgeCode
  rw [shiftedMeshPath_time_dilation w w' b d θ hw]

end LatticeProb
