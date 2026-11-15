import LatticeProb.LQG.ShiftedMeshVertexWalkLaw
import LatticeProb.LQG.ScaledWalkWitnessEvent

/-! # Jointly measurable shifted walk witnesses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal NNReal

namespace LatticeProb

/-- Boundary path and geometric witness parameters. -/
abbrev JointShiftedWalkWitness := MatedCRT.Path2 × ScaledWalkWitness

/-- Extract the boundary path, mesh, shift, and starting vertex. -/
def jointShiftedMeshParameter (q : JointShiftedWalkWitness) : ShiftedMeshParameter :=
  ((q.1, q.2.1.1.2.1, q.2.1.1.2.2), q.2.2.2)

/-- The graph parameters are measurable in the joint witness. -/
theorem measurable_jointShiftedMeshParameter : Measurable jointShiftedMeshParameter := by
  exact (measurable_fst.prodMk (measurable_snd.fst.fst.snd.fst.prodMk
    measurable_snd.fst.fst.snd.snd)).prodMk measurable_snd.snd.snd

/-- The vertex walk kernel indexed by the boundary path and geometric witness. -/
def jointShiftedVertexWalkKernel : Kernel JointShiftedWalkWitness (ℕ → ℤ) :=
  shiftedMeshVertexWalkKernel.comap jointShiftedMeshParameter measurable_jointShiftedMeshParameter

instance : IsFiniteKernel jointShiftedVertexWalkKernel := by
  unfold jointShiftedVertexWalkKernel
  infer_instance

/-- At a locally finite boundary path, the kernel is the graph walk vertex law. -/
theorem jointShiftedVertexWalkKernel_apply (q : JointShiftedWalkWitness)
    (h : MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2)) :
    jointShiftedVertexWalkKernel q =
      ((MatedCRT.graph 1 (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2) h).walkLaw
        q.2.2.2).map
        (MatedCRT.graph 1 (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2) h).vertexPath := by
  exact shiftedMeshVertexWalkKernel_apply (jointShiftedMeshParameter q) h

/-- Outside local finiteness the kernel has zero mass. -/
theorem jointShiftedVertexWalkKernel_apply_of_not_locallyFinite (q : JointShiftedWalkWitness)
    (h : ¬ MatedCRT.IsLocallyFinite 1
      (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2)) :
    jointShiftedVertexWalkKernel q = 0 := by
  exact shiftedMeshVertexWalkKernel_apply_of_not_locallyFinite (jointShiftedMeshParameter q) h

set_option maxHeartbeats 400000 in
/-- The interpolated path is jointly measurable in the witness and walk. -/
theorem measurable_jointShiftedWalkPath :
    Measurable (fun z : JointShiftedWalkWitness × (ℕ → ℤ) =>
      scaledWalkPath z.1.2 z.2) := by
  have hp : Measurable (fun z : JointShiftedWalkWitness × (ℕ → ℤ) =>
      (z.1.2, z.2)) := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def] using measurable_scaledWalkPath.comp hp

/-- Probabilities of jointly Borel path events are measurable in the witness. -/
theorem measurable_jointShiftedWalk_event_probability
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U) :
    Measurable (fun q : JointShiftedWalkWitness =>
      jointShiftedVertexWalkKernel q {ξ | (q, scaledWalkPath q.2 ξ) ∈ U}) := by
  exact jointShiftedVertexWalkKernel.measurable_kernel_prodMk_left
    (hU.preimage (measurable_fst.prodMk measurable_jointShiftedWalkPath))

/-- A scaled anchor constraint and a bound on a path-event probability form
 a measurable witness relation. -/
theorem measurableSet_jointShiftedWalk_witness
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞) :
    MeasurableSet {q : JointShiftedWalkWitness | scaledWalkStart q.2 ∈ K ∧
      jointShiftedVertexWalkKernel q {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} ≤ t} :=
  (hK.preimage (measurable_scaledWalkStart.comp measurable_snd)).inter
    (measurableSet_le (measurable_jointShiftedWalk_event_probability hU) measurable_const)

end LatticeProb
