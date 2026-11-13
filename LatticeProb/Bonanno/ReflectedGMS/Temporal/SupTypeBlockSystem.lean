/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.SupTypeBlockSystem at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SupTypeTimeBlocks
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystemGated

/-!
# The sup-type blocks assemble into the gated root-chain system

Section 17 of the singular-set manuscript, assembled: the blocks `supBlock` of
`SupTypeTimeBlocks` (the manuscript's `J_m(s)`, with the null-set convention at the times without
a good block) satisfy every field of the a.e.-time `TemporalBlockSystem`
(`temporalBlockSystem_supBlock`) and of `GatedRootChainBlocks` (`gatedRootChainBlocks_supBlock`),
carrier-generically under `HoldingData G θΩ SΩ hold`; with the unmarked-plus-grid transport and the
two almost-sure clauses on the law — the environment gate is conull and the origin is a vertex
time — they give `ScaledRootChainSystemOn` (`scaledRootChainSystemOn_of_holdingData`).

Compared with `FlowSpaceBlockSystem.gatedRootChainBlocks_of_localTimeScaleOn`, NO positive lower
bound on any scale along the path is required: the only law-level inputs are the invariant gate
being conull and `∀ᵐ ω, hold ω 0 ≠ 0` (the origin lies in a holding interval), which at the rooted
law is the fixed-time definedness of the walk at time `0`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal NNReal

namespace ReflectedGMS.SupTypeBlockSystem

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance
open ReflectedGMS.Temporal.ActualDyadicTemporalBlocks ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.GridAveragedInvariantVersion ReflectedGMS.ConditionalTemporalAveraging
open ReflectedGMS.ScaledConditionalTemporalAveraging ReflectedGMS.ParabolicTransport
open ReflectedGMS.ScaledRootChainGated
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.SupTypeTimeIndex ReflectedGMS.SupTypeTimeBlocks

variable {Ω : Type*} [MeasurableSpace Ω] (hold : Ω → ℝ → ℝ≥0∞) {G : Set Ω}
  {θΩ SΩ : ℝ → Ω → Ω} (hd : HoldingData G θΩ SΩ hold)
include hd

/-- **Every field of the (a.e.-time) `TemporalBlockSystem` for the sup-type blocks.** -/
theorem temporalBlockSystem_supBlock {θ : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (h0 : ∀ p : Ω × Grid, θ 0 p = p) (hadd : ∀ (a b : ℝ) (p : Ω × Grid), θ a (θ b p) = θ (a + b) p)
    (hmeas : Measurable fun p : (Ω × Grid) × ℝ => θ p.2 p.1) (q : ℚ) :
    TemporalBlockSystem θ (supBlock hold G q) where
  flow_zero := h0
  flow_add := hadd
  measurable_flow := hmeas
  self_mem := fun p s => self_mem_supBlock hold q p s
  block_eq := fun _ _ _ ht => supBlock_eq_of_mem hold hd ht
  shift := fun p r s => supBlock_shift hold hd hθ q p r s
  measurableSet_graph := measurableSet_graph_supBlock hold hd q
  volume_pos_ae := fun p => volume_supBlock_pos_ae hold hd q p
  volume_lt_top := fun p s => volume_supBlock_lt_top hold q p s

/-- **The gated block data for the sup-type blocks.** -/
theorem gatedRootChainBlocks_supBlock {θ S : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    (h0 : ∀ p : Ω × Grid, θ 0 p = p) (hadd : ∀ (a b : ℝ) (p : Ω × Grid), θ a (θ b p) = θ (a + b) p)
    (hmeas : Measurable fun p : (Ω × Grid) × ℝ => θ p.2 p.1) :
    GatedRootChainBlocks G θ S (supBlock hold G) (supSel hold hd) where
  system := temporalBlockSystem_supBlock hold hd hθ h0 hadd hmeas
  nested := fun _ _ hq p => supBlock_nested hold hd hq p
  blockScaleOn := fun q _ hC _ hp s => supBlock_scale_of_mem hold hd hS q hC hp s
  selection_tendsto := tendsto_supSel hold hd
  selection_root := selection_root_supSel hold hd

/-- **The gated root-chain system from the holding data**: the marked transport, a conull gate and
the origin being a vertex time almost surely.  No lower bound on a time scale along the path. -/
theorem scaledRootChainSystemOn_of_holdingData {P : Measure Ω} {ν : Measure Grid} [SFinite ν]
    {θ S : ℝ → Ω × Grid → Ω × Grid}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    (h0 : ∀ p : Ω × Grid, θ 0 p = p) (hadd : ∀ (a b : ℝ) (p : Ω × Grid), θ a (θ b p) = θ (a + b) p)
    (hmeas : Measurable fun p : (Ω × Grid) × ℝ => θ p.2 p.1)
    (hflow : FlowScaleIntertwine θ S) (htr : ParabolicTemporalTransport (P.prod ν) θ S)
    (hae : ∀ᵐ ω ∂P, ω ∈ G) (horigin : ∀ᵐ ω ∂P, ω ∈ G → hold ω 0 ≠ 0) :
    ScaledRootChainSystemOn (Prod.fst ⁻¹' G) P ν θ S (supBlock hold G) (supSel hold hd) := by
  refine scaledRootChainSystemOn_of_gatedRootChainBlocks
    (gatedRootChainBlocks_supBlock hold hd hθ hS h0 hadd hmeas) hflow htr hθ hS
    hd.measurableSet_gate (fun t => Set.ext fun ω => hd.flow_mem t ω)
    (fun C hC => Set.ext fun ω => hd.scale_mem C hC ω) hae fun q => ?_
  have hlift : ∀ᵐ p ∂(P.prod ν), p.1 ∈ G → hold p.1 0 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae horigin
  filter_upwards [hlift] with p hp
  exact volume_supBlock_pos_of_ne_zero hold hd q p hp

end ReflectedGMS.SupTypeBlockSystem

#print axioms ReflectedGMS.SupTypeBlockSystem.temporalBlockSystem_supBlock
#print axioms ReflectedGMS.SupTypeBlockSystem.gatedRootChainBlocks_supBlock
#print axioms ReflectedGMS.SupTypeBlockSystem.scaledRootChainSystemOn_of_holdingData
