/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowGateRootChainGate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystemGated
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGateFlow

/-!
# `flowGate` meets the gate conditions of `ScaledRootChainSystemOn`

`Limit/ScaledRootChainSystemGated.ScaledRootChainSystemOn G …` asks of its gate `G ⊆ Ω × Grid`:
measurable, preserved exactly by every marked time shift `θ t` and every positive marked scaling
`S C`, and conull for the marked law `P ⊗ ν`.  On the flow carrier
`FlowSpace = Env × FlowCoding` with the marked flow `gridFlow` and scaling `gridScaleFlow`
(`Temporal/TwoSidedRegenerationFlowGrid`), the natural gate is the environment-coordinate gate
`Temporal/SimilarityClosedGateFlow.flowGate`, marked: `markedFlowGate := Prod.fst ⁻¹' flowGate`.

* `invariantGate_markedFlowGate`: measurable and invariant (from `preimage_reRootFlow_flowGate`,
  `preimage_reScale_flowGate`; every `C`, not only `C > 0`).
* `ae_mem_flowGate_of_marginal`, `ae_mem_markedFlowGate_of_marginal`: conull for EVERY law `Q` on
  `FlowSpace` whose environment marginal is absolutely continuous w.r.t. an MTP+FE law — hence
  independent of the origin- vs cell-rooting decision, provided the chosen rooted law has an
  environment marginal `≪ ν` (the origin-rooted `ν ⊗ₘ κ` has marginal exactly `ν`:
  `ae_mem_markedFlowGate_compProd`).
* `not_exists_scaleFixed_mem_markedFlowGate` (via `eq_one_of_isSimilarity_self_of_mem`): no point
  of the gate is fixed by a nontrivial scaling, so the gated obstruction
  `ScaledRootChainGated.false_of_scaleFixed_mem` cannot fire on this gate (the seventh trap does
  not recur inside `flowGate`).
* `scaledRootChainSystemOn_markedFlowGate`: `ScaledRootChainSystemOn markedFlowGate Q gridMeasure
  gridFlow gridScaleFlow blkFam sel` from the gated block data
  (`FlowSpaceBlockSystem.GatedRootChainBlocks flowGate …`, the output of
  `gatedRootChainBlocks_of_localTimeScaleOn`), the UNMARKED transport
  `ParabolicTemporalTransport Q reRootFlow reScale`, and the marginal condition.  The marked
  transport is averaged in by `parabolicTemporalTransport_prod_of_uniformGridLaw`.

Not provided: a `LocalTimeScaleOn flowGate reRootFlow reScale τ` (the concrete gated time scale;
`FlowSpaceBlockSystem` handoff §4.2) and the unmarked transport at the actual law.
-/

set_option autoImplicit false

open MeasureTheory Set ProbabilityTheory

open scoped ENNReal NNReal Pointwise

namespace ReflectedGMS.FlowGateRootChainGate

open Code EnvironmentLaws HarmonicLawIngredients
open ReflectedGMS.SimilarityClosedGate ReflectedGMS.SimilarityClosedGateFlow
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.DyadicApproximation ReflectedGMS.ScaledRootChain
open ReflectedGMS.ScaledRootChainGated ReflectedGMS.ParabolicTransport
open ReflectedGMS.TemporalMassTransport ReflectedGMS.Spatial

/-- The marked flow gate: the environment coordinate lies in the similarity-closed gate. -/
def markedFlowGate : Set (FlowSpace × Grid) := Prod.fst ⁻¹' flowGate

/-! ### 3. The gate contains no scale-fixed point

`ScaledRootChainGated.false_of_scaleFixed_mem`: a scale-fixed point INSIDE the gate refutes the
gated covariance just as a fixed point anywhere refuted the ungated one.  So the gated structure
on `markedFlowGate` is only non-vacuous if no point of the gate is fixed by a nontrivial
scaling.  That is proved here: a gate environment fixed by `z ↦ C z` would have the cells through
the origin (finitely bounded by `maxDiamHittingBall · 1 < ∞`, positive by the nonempty interior)
with supremal diameter `M` satisfying `M ≥ C M` and `M ≥ C⁻¹ M`, so `C = 1`.  (The
self-similar `e*` of the `FlowSpaceBlockSystem` handoff has `maxDiamHittingBall e* 1 = ∞`.) -/

end ReflectedGMS.FlowGateRootChainGate
