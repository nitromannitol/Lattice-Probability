import LatticeProb.LQG.ShiftedMeshWalkLaw
import Mathlib.Probability.Kernel.Composition.MapComap

/-! # Vertex walk laws on shifted meshes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling

namespace LatticeProb

/-- Decode each state of a coded path to its graph vertex. -/
def meshGridVertexPath (path : ℕ → MeshGridStateCode) : ℕ → ℤ :=
  fun i => meshGridStateVertexCode (path i)

/-- Coordinatewise decoding is measurable on path space. -/
theorem measurable_meshGridVertexPath : Measurable meshGridVertexPath := by
  apply Measurable.of_eval
  intro i
  exact Measurable.of_discrete.comp (measurable_pi_apply i)

/-- The shifted graph vertex-path law, extended by zero off local finiteness. -/
def shiftedMeshVertexWalkKernel : Kernel ShiftedMeshParameter (ℕ → ℤ) :=
  shiftedMeshCodedWalkKernel.map meshGridVertexPath

instance : IsFiniteKernel shiftedMeshVertexWalkKernel := by
  unfold shiftedMeshVertexWalkKernel
  infer_instance

/-- On the local-finiteness domain, decoding the kernel gives the graph's
vertex-path walk law, including all edge multiplicities. -/
theorem shiftedMeshVertexWalkKernel_apply (p : ShiftedMeshParameter)
    (h : MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)) :
    shiftedMeshVertexWalkKernel p =
      ((MatedCRT.graph 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) h).walkLaw p.2).map
        (MatedCRT.graph 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) h).vertexPath := by
  classical
  rw [shiftedMeshVertexWalkKernel, Kernel.map_apply _ measurable_meshGridVertexPath]
  change Measure.map meshGridVertexPath (shiftedMeshCodedWalkLaw p) = _
  rw [shiftedMeshCodedWalkLaw, dite_eq_left h]
  have henc : Measurable (fun path : ℕ → (MatedCRT.graph 1
      (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2) h).State =>
      fun i => meshGridEncodeMatedState (path i)) := by
    apply Measurable.of_eval
    intro i
    exact Measurable.of_discrete.comp (measurable_pi_apply i)
  rw [Measure.map_map measurable_meshGridVertexPath henc]
  congr 1
  funext path i
  exact meshGridStateVertexCode_encode (path i)

/-- The vertex-walk kernel is zero outside the local-finiteness domain. -/
theorem shiftedMeshVertexWalkKernel_apply_of_not_locallyFinite (p : ShiftedMeshParameter)
    (h : ¬ MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1.1 p.1.2.1 p.1.2.2)) :
    shiftedMeshVertexWalkKernel p = 0 := by
  classical
  rw [shiftedMeshVertexWalkKernel, Kernel.map_apply _ measurable_meshGridVertexPath]
  change Measure.map meshGridVertexPath (shiftedMeshCodedWalkLaw p) = 0
  simp [shiftedMeshCodedWalkLaw, h]

end LatticeProb
