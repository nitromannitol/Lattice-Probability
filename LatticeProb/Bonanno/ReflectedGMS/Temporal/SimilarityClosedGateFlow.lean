/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.SimilarityClosedGateFlow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGate
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationFlow
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockSimilarity
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernelMeasurability

/-!
# The similarity-closed gate on the flow carrier, and `law_φ` at EVERY similar pair

Consumers of `SimilarityClosedGate.similarityClosedGate`:

1. **The flow and the scaling.**  `flowGate = Prod.fst ⁻¹' similarityClosedGate ⊆ FlowSpace` is
   measurable and EXACTLY invariant (preimage equal to itself, at every point) under the
   re-rooting flow `TwoSidedRegenerationFlow.reRootFlow t` (environment map
   `translateEnv (displacement ω t)`, a translation by an arbitrary real vector), the scaling
   `reScale C` (environment map `similarityTargetEnv C 0` for `C > 0`, the identity otherwise),
   the frame change `reFrame u`, the rooting map `rootMap c` and the plain shift `plainShift t`.
2. **The gated laws.**  For ANY gate `G` of admissible environments with `e ∈ G ↔ e' ∈ G` at a
   similar pair, the similarity covariance of the gated label law and two-sided law holds with
   no membership hypothesis (`slotLaw_similarity_of_iff`, `twoSidedSlotLaw_similarity_of_iff`):
   outside the gate both sides are the cemetery Dirac, and the cemetery is fixed by the
   dilation.  Hence the `law_φ` equation of `ActualConditionalPathIntegral.DilationCoding` holds
   at EVERY similar pair for the closed gate (`law_φ_of_twoSidedCoding_closedGate`), which is
   false for a non-closed gate (`outputs/area-clock-similarity-handoff.2026-09-18.md`, item 1).
3. **The kernel.**  `closedGateKernel = regenerationKernel similarityClosedGate …` is the
   regeneration kernel at the closed gate (no remaining input: `hmeas` is
   `RegenerationKernelMeasurability.measurable_slotTransition`).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.SimilarityClosedGateFlow

open Code EnvironmentLaws
open ReflectedGMS.SimilarityClosedGate ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TrajectoryCoding ReflectedGMS.ActualMarkedBlockTransport
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedWalk ReflectedWalk.Theorem16

/-! ### 1. The gate on the flow carrier -/

/-- The flow-carrier gate: the environment coordinate lies in the closed gate. -/
def flowGate : Set FlowSpace := Prod.fst ⁻¹' similarityClosedGate

theorem mem_flowGate_iff (ω : FlowSpace) : ω ∈ flowGate ↔ ω.1 ∈ similarityClosedGate := Iff.rfl

theorem measurableSet_flowGate : MeasurableSet flowGate :=
  measurable_fst measurableSet_similarityClosedGate

theorem reFrame_mem_flowGate_iff (u : Plane) (ω : FlowSpace) :
    reFrame u ω ∈ flowGate ↔ ω ∈ flowGate :=
  translateEnv_mem_similarityClosedGate_iff u ω.1

/-- **The re-rooting flow preserves the gate exactly, at every point.** -/
theorem reRootFlow_mem_flowGate_iff (t : ℝ) (ω : FlowSpace) :
    reRootFlow t ω ∈ flowGate ↔ ω ∈ flowGate :=
  translateEnv_mem_similarityClosedGate_iff (displacement ω t) ω.1

/-- **The parabolic scaling preserves the gate exactly, at every point and every `C`.** -/
theorem reScale_mem_flowGate_iff (C : ℝ) (ω : FlowSpace) :
    reScale C ω ∈ flowGate ↔ ω ∈ flowGate := by
  by_cases hC : 0 < C
  · rw [mem_flowGate_iff, mem_flowGate_iff, reScale_fst hC]
    exact similarityTargetEnv_mem_similarityClosedGate_iff C 0 hC ω.1
  · have h : reScale C ω = ω := by
      unfold reScale
      rw [dite_eq_right hC]
    rw [h]

theorem rootMap_mem_flowGate_iff (c : Env → Plane) (ω : FlowSpace) :
    rootMap c ω ∈ flowGate ↔ ω ∈ flowGate :=
  reFrame_mem_flowGate_iff _ ω

theorem preimage_reRootFlow_flowGate (t : ℝ) : reRootFlow t ⁻¹' flowGate = flowGate :=
  Set.ext fun ω => reRootFlow_mem_flowGate_iff t ω

theorem preimage_reScale_flowGate (C : ℝ) : reScale C ⁻¹' flowGate = flowGate :=
  Set.ext fun ω => reScale_mem_flowGate_iff C ω

/-! ### 2. The gated laws at every similar pair -/

section Laws

open ReflectedGMS.AreaClockSimilarity ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.ReflectedWalkDilation

variable {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
  {relabel : Vertex e.val ≃ Vertex e'.val}

/-- The cemetery trajectory is fixed by every dilation. -/
theorem dilateTraj_cemetery (lab : ℕ → ℕ) (a : ℝ≥0) : dilateTraj lab a cemetery = cemetery :=
  rfl

/-- **Similarity covariance of the gated forward label law, with no membership hypothesis**,
for any gate that contains both or neither environment of the pair. -/
theorem slotLaw_similarity_of_iff {G : Set Env}
    (hGadm : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (h : IsSimilarityRelabel s u hs e e' relabel) (hG : e ∈ G ↔ e' ∈ G)
    (lab : ℕ → ℕ) (hlab : ∀ v : Vertex e.val, lab v.val = (relabel v).val) (v : Vertex e.val) :
    slotLaw G (relabel v).val e'
      = (slotLaw G v.val e).map (dilateTraj lab (parabolicFactor s)) := by
  by_cases he : e ∈ G
  · exact slotLaw_similarity hGadm h he (hG.1 he) lab hlab v
  · have he' : e' ∉ G := fun h' => he (hG.2 h')
    rw [slotLaw_of_not (fun hh => he' hh.1), slotLaw_of_not (fun hh => he hh.1),
      Measure.map_dirac' (measurable_dilateTraj _ _), dilateTraj_cemetery]

/-- **Similarity covariance of the gated two-sided law, with no membership hypothesis.** -/
theorem twoSidedSlotLaw_similarity_of_iff {G : Set Env}
    (hGadm : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (h : IsSimilarityRelabel s u hs e e' relabel) (hG : e ∈ G ↔ e' ∈ G)
    (lab : ℕ → ℕ) (hlab : ∀ v : Vertex e.val, lab v.val = (relabel v).val) (v : Vertex e.val) :
    twoSidedSlotLaw G (relabel v).val e'
      = (twoSidedSlotLaw G v.val e).map
          (Prod.map (dilateTraj lab (parabolicFactor s)) (dilateTraj lab (parabolicFactor s))) := by
  unfold twoSidedSlotLaw
  rw [slotLaw_similarity_of_iff hGadm h hG lab hlab v]
  exact Measure.map_prod_map _ _ (measurable_dilateTraj _ _) (measurable_dilateTraj _ _)

end Laws

/-! ### 3. The regeneration kernel at the closed gate -/

end ReflectedGMS.SimilarityClosedGateFlow
