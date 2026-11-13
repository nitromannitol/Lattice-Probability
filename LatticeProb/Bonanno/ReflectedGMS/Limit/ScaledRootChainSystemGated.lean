/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ScaledRootChainSystemGated at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystem
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceBlockSystem

/-!
# The root chain system with `blockScale` GATED on an invariant conull set

`Limit/ScaledRootChainSystem.ScaledRootChainSystem` requires the parabolic block covariance
`blockScale` **at every point** of the carrier.  `Temporal/FlowSpaceBlockSystem` shows that this is
a vacuity trap: at any point `p` with `S_C p = p` (`C ≠ 1`) the field forces `B = C²·B` for the
origin block, contradicting `0 < |B| < ∞` (`not_scaledRootChainSystem_of_scaleFixed`), and the
flow carrier has such points as soon as one valid environment is self-similar.  The actual law
never sees those points: they lie outside a measurable set `G`, invariant under the flow and the
scaling, of full measure.

This module gates `blockScale` on such a `G` and re-proves every consumer, carrier-generically.

## The transfer ("restrict every functional to `G`")

`blockScale` has exactly one consumer, the parabolic covariance of the manuscript kernel
`V(ω,s,t) = |J(s)|⁻¹ 1_{t ∈ J(s)} F(θ_t ω)`
(`ScaledConditionalTemporalAveraging.parabolicCovariantReal_blockTransportReal`).  For `F` vanishing
off an invariant `G`, the kernel is covariant everywhere when the blocks are covariant on `G`
(`FlowSpaceBlockSystem.parabolicCovariantReal_blockTransportReal_of_gate`: on `Gᶜ` both sides are
`0`).  So the conditional-averaging chain runs for `1_G · F` (§2), and since `G` is conull and
flow invariant, `1_G · F = F` almost surely and along every flow line through `G`; the
conditional expectations agree a.e.  The chain limit for `F` itself follows
(`tendsto_setAverageReal_chain_ae_of_transport_gated`, §3), with conclusion **character for
character** that of the ungated `tendsto_setAverageReal_chain_ae_of_transport`.

## What is proved

* `InvariantGate θ S G`, `ScaleCovariantBlocksOn G S blk`, `ScaledRootChainSystemOn G P ν θ S
  blkFam sel` (the old structure, `blockScale` required on `G` only, plus the gate fields).
* `scaledRootChainSystemOn_univ` (ungated ⇒ gated at `G = univ`) and
  `scaledRootChainSystem_iff_on_univ` (the gated structure at `univ` IS the old one).
* `scaledRootChainSystemOn_of_gatedRootChainBlocks`: the gated structure from
  `FlowSpaceBlockSystem.GatedRootChainBlocks` (the handoff's gated block constructor) with the
  environment-coordinate gate `Prod.fst ⁻¹' G₀`.
* `false_of_scaleFixed_mem`: the obstruction survives inside the gate, so a gate must exclude
  every scale-fixed point (documents what `G` is for; `flowGate` does, see
  `Temporal/FlowGateRootChainGate`).
* §4: every consumer of `ScaledRootChainSystem` in `Limit/ScaledRootChainSystem`, gated, with
  identical conclusions: `ae_hasRootBlockData_of_scaledSystemOn`,
  `gridAveragedConstant_of_scaledRootChainSystemOn`,
  `ae_hasRootBlockData_of_regenerativeInvariance_scaledOn`,
  `ae_tendsto_intervalAverage_of_regenerativeInvariance_scaledOn`.

## Satisfiability of the new fields

`gate`, `gate_ae`: `G = univ` always (so every old system is a gated one); on the flow carrier
`Prod.fst ⁻¹' flowGate` for every law whose environment marginal is `≪` an MTP+FE law
(`Temporal/FlowGateRootChainGate`).  `blockScaleOn` is WEAKER than `blockScale` and is what
`FlowSpaceBlockSystem.gatedRootChainBlocks_of_localTimeScaleOn` produces.

Nothing here constructs a `ScaledRootChainSystemOn` at the actual annealed law.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

open scoped ENNReal

namespace ReflectedGMS.ScaledRootChainGated

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridDilationInvariance ReflectedGMS.UniformGridTranslationInvariance
open ReflectedGMS.BracketTimeAverage ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.ConditionalTemporalAveraging ReflectedGMS.TailAverageIdentification
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ParabolicTransport
open ReflectedGMS.ScaledConditionalTemporalAveraging ReflectedGMS.ScaledRootChain

/-! ## 1. The gate and gated covariance -/

section Gate

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **An invariant gate**: a measurable set preserved exactly (preimage equality) by every time
shift `θ t` and every positive parabolic scaling `S C`. -/
structure InvariantGate (θ S : ℝ → Ω → Ω) (G : Set Ω) : Prop where
  /-- The gate is measurable. -/
  measurableSet : MeasurableSet G
  /-- The gate is invariant under every time shift. -/
  flow : ∀ t : ℝ, θ t ⁻¹' G = G
  /-- The gate is invariant under every positive scaling. -/
  scale : ∀ C : ℝ, 0 < C → S C ⁻¹' G = G

theorem InvariantGate.flow_mem_iff {θ S : ℝ → Ω → Ω} {G : Set Ω} (hG : InvariantGate θ S G)
    (t : ℝ) (ω : Ω) : θ t ω ∈ G ↔ ω ∈ G := by
  rw [← Set.mem_preimage, hG.flow t]

theorem InvariantGate.scale_mem_iff {θ S : ℝ → Ω → Ω} {G : Set Ω} (hG : InvariantGate θ S G)
    {C : ℝ} (hC : 0 < C) (ω : Ω) : S C ω ∈ G ↔ ω ∈ G := by
  rw [← Set.mem_preimage, hG.scale C hC]

/-- **Parabolic covariance of a block system on a gate**: `J^{S_C ω}(C²s) = C² · J^ω(s)` for
`ω ∈ G` only. -/
def ScaleCovariantBlocksOn (G : Set Ω) (S : ℝ → Ω → Ω) (blk : Ω → ℝ → Set ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ω ∈ G, ∀ s : ℝ,
    blk (S C ω) (C ^ 2 * s) = (fun x : ℝ => C ^ 2 * x) '' blk ω s

end Gate

/-! ## 2. The conditional-averaging chain for functionals vanishing off the gate -/

section Averaging

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {θ S : ℝ → Ω → Ω} {blk : Ω → ℝ → Set ℝ} {G : Set Ω}

/-- **The kernel is covariant everywhere** for `F` vanishing off an invariant gate on which the
blocks are covariant (the gated replacement of the only consumer of `blockScale`). -/
theorem parabolicCovariantReal_blockTransportReal_gate (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S) {F : Ω → ℝ}
    (hF : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    ParabolicCovariantReal S (blockTransportReal θ blk F) :=
  FlowSpaceBlockSystem.parabolicCovariantReal_blockTransportReal_of_gate hG.flow_mem_iff
    (fun _ hC ω => hG.scale_mem_iff hC ω) hblk hflow hF hFG

/-- The block average of such an `F` is scale invariant. -/
theorem blockAverageReal_scale_gate (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S) {F : Ω → ℝ}
    (hF : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) {C : ℝ} (hC : 0 < C) (ω : Ω) :
    blockAverageReal θ blk F (S C ω) = blockAverageReal θ blk F ω := by
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hker := parabolicCovariantReal_blockTransportReal_gate hG hblk hflow hF hFG C hC ω 0
  rw [← h.integral_blockTransportReal_outgoing F (S C ω),
    ← h.integral_blockTransportReal_outgoing F ω]
  have hcv : ∫ x : ℝ, blockTransportReal θ blk F (S C ω) 0 (C ^ 2 * x)
      = |(C ^ 2)⁻¹| • ∫ y : ℝ, blockTransportReal θ blk F (S C ω) 0 y :=
    Measure.integral_comp_mul_left _ _
  have hpt : ∀ x : ℝ, blockTransportReal θ blk F (S C ω) 0 (C ^ 2 * x)
      = (C ^ 2)⁻¹ * blockTransportReal θ blk F ω 0 x := by
    intro x
    have := hker x
    rwa [mul_zero] at this
  simp only [hpt, integral_const_mul, abs_of_pos (inv_pos.2 hC2), smul_eq_mul] at hcv
  exact (mul_left_cancel₀ (inv_ne_zero hC2.ne') hcv).symm

/-- `A_m` is `𝒢_m`-measurable. -/
theorem measurable_reRootScaleSigma_blockAverageReal_gate (h : TemporalBlockSystem θ blk)
    (hG : InvariantGate θ S G) (hblk : ScaleCovariantBlocksOn G S blk)
    (hflow : FlowScaleIntertwine θ S) {F : Ω → ℝ} (hFm : Measurable F) (hFs : ScaleInvariant S F)
    (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    Measurable[reRootScaleSigma θ S blk] (blockAverageReal θ blk F) :=
  measurable_reRootScaleSigma_of_invariant (h.measurable_blockAverageReal hFm)
    (fun ω _ ht => h.blockAverageReal_shift F ω ht)
    (fun _ hC ω => blockAverageReal_scale_gate h hG hblk hflow hFs hFG hC ω)

section Law

variable {P : Measure Ω} {F : Ω → ℝ}

theorem integrable_blockTransportReal_outgoing_of_transport_gate [SFinite P]
    (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S)
    (htr : ParabolicTemporalTransport P θ S) (hFm : Measurable F) (hF : Integrable F P)
    (hFs : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    Integrable (fun p : Ω × ℝ => blockTransportReal θ blk F p.1 0 p.2) (P.prod volume) :=
  (ParabolicTransport.integrable_outgoing_iff_incoming htr (blockTransportReal θ blk F)
    (h.measurable_blockTransportReal hFm) (h.timeShiftCovariant_blockTransportReal F)
    (parabolicCovariantReal_blockTransportReal_gate hG hblk hflow hFs hFG)).2
    (h.integrable_blockTransportReal_incoming hFm hF)

theorem integrable_blockAverageReal_of_transport_gate [SFinite P]
    (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S)
    (htr : ParabolicTemporalTransport P θ S) (hFm : Measurable F) (hF : Integrable F P)
    (hFs : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    Integrable (blockAverageReal θ blk F) P := by
  have hbase := (integrable_blockTransportReal_outgoing_of_transport_gate h hG hblk hflow htr hFm
    hF hFs hFG).integral_prod_left
  refine hbase.congr ?_
  filter_upwards with ω
  exact h.integral_blockTransportReal_outgoing F ω

/-- The block-averaging identity of `p:lem:timeconditional`, for `F` vanishing off the gate, for
a law under which the origin block almost surely has positive length (`h0`). -/
theorem integral_blockAverageReal_of_transport_gate [SFinite P]
    (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S)
    (htr : ParabolicTemporalTransport P θ S) (h0 : ∀ᵐ ω ∂P, 0 < volume (blk ω 0))
    (hFm : Measurable F) (hF : Integrable F P)
    (hFs : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    ∫ ω, blockAverageReal θ blk F ω ∂P = ∫ ω, F ω ∂P := by
  have key := ParabolicTransport.integral_integral_timeTransport htr (blockTransportReal θ blk F)
    (h.measurable_blockTransportReal hFm) (h.timeShiftCovariant_blockTransportReal F)
    (parabolicCovariantReal_blockTransportReal_gate hG hblk hflow hFs hFG)
    (integrable_blockTransportReal_outgoing_of_transport_gate h hG hblk hflow htr hFm hF hFs hFG)
  calc ∫ ω, blockAverageReal θ blk F ω ∂P
      = ∫ ω, ∫ t : ℝ, blockTransportReal θ blk F ω 0 t ∂(volume : Measure ℝ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        exact (h.integral_blockTransportReal_outgoing F ω).symm
    _ = ∫ ω, ∫ s : ℝ, blockTransportReal θ blk F ω s 0 ∂(volume : Measure ℝ) ∂P := key
    _ = ∫ ω, F ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h0] with ω hω
        exact h.integral_blockTransportReal_incoming F ω hω

/-- The set-integral identity over a `𝒢_m`-event, for `F` vanishing off the gate (the indicator
of the event keeps vanishing off the gate). -/
theorem setIntegral_blockAverageReal_of_transport_gate [SFinite P]
    (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S)
    (htr : ParabolicTemporalTransport P θ S) (h0 : ∀ᵐ ω ∂P, 0 < volume (blk ω 0))
    (hFm : Measurable F) (hF : Integrable F P)
    (hFs : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) {B : Set Ω}
    (hB : MeasurableSet[reRootScaleSigma θ S blk] B) :
    ∫ ω in B, blockAverageReal θ blk F ω ∂P = ∫ ω in B, F ω ∂P := by
  have hBm : MeasurableSet B := hB.1
  rw [← integral_indicator hBm, ← integral_indicator hBm]
  calc ∫ ω, B.indicator (blockAverageReal θ blk F) ω ∂P
      = ∫ ω, blockAverageReal θ blk (B.indicator F) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        exact (h.blockAverageReal_indicator F hB.2.1 ω).symm
    _ = ∫ ω, B.indicator F ω ∂P :=
        integral_blockAverageReal_of_transport_gate h hG hblk hflow htr h0 (hFm.indicator hBm)
          (hF.indicator hBm) (scaleInvariant_indicator hFs hB.2.2)
          (fun ω hω => Set.indicator_apply_eq_zero.2 fun _ => hFG ω hω)

/-- `p:eq:timeconditional` for `F` vanishing off the gate. -/
theorem blockAverageReal_ae_eq_condExp_of_transport_gate [IsProbabilityMeasure P]
    (h : TemporalBlockSystem θ blk) (hG : InvariantGate θ S G)
    (hblk : ScaleCovariantBlocksOn G S blk) (hflow : FlowScaleIntertwine θ S)
    (htr : ParabolicTemporalTransport P θ S) (h0 : ∀ᵐ ω ∂P, 0 < volume (blk ω 0))
    (hFm : Measurable F) (hF : Integrable F P)
    (hFs : ScaleInvariant S F) (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    blockAverageReal θ blk F =ᵐ[P] P[F|reRootScaleSigma θ S blk] := by
  have hle : reRootScaleSigma θ S blk ≤ m0 := reRootScaleSigma_le θ S blk
  have : IsFiniteMeasure (P.trim hle) := by
    refine ⟨?_⟩
    rw [trim_measurableSet_eq hle (@MeasurableSet.univ Ω (reRootScaleSigma θ S blk))]
    exact measure_lt_top P Set.univ
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hF ?_ ?_ ?_
  · intro s _ _
    exact (integrable_blockAverageReal_of_transport_gate h hG hblk hflow htr hFm hF hFs
      hFG).integrableOn
  · intro s hs _
    exact setIntegral_blockAverageReal_of_transport_gate h hG hblk hflow htr h0 hFm hF hFs hFG hs
  · exact (measurable_reRootScaleSigma_blockAverageReal_gate h hG hblk hflow hFm hFs
      hFG).stronglyMeasurable.aestronglyMeasurable

end Law

end Averaging

/-! ## 3. The complete dyadic chain, and the transfer to every scale-invariant functional -/

section Convergence

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {θ S : ℝ → Ω → Ω} {blkFam : ℚ → Ω → ℝ → Set ℝ} {G : Set Ω} {P : Measure Ω}
  {F : Ω → ℝ}

theorem tendsto_blockAverageReal_ae_of_transport_gate [IsProbabilityMeasure P]
    (h : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q))
    (hmono : ∀ q q' : ℚ, q ≤ q' → ∀ ω : Ω, blkFam q ω 0 ⊆ blkFam q' ω 0)
    (hG : InvariantGate θ S G) (hblk : ∀ q : ℚ, ScaleCovariantBlocksOn G S (blkFam q))
    (hflow : FlowScaleIntertwine θ S) (htr : ParabolicTemporalTransport P θ S)
    (h0 : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < volume (blkFam q ω 0))
    (hFm : Measurable F) (hF : Integrable F P) (hFs : ScaleInvariant S F)
    (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun q : ℚ => blockAverageReal θ (blkFam q) F ω) atTop
      (𝓝 (P[F|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)] ω)) := by
  have hle : ∀ q : ℚ, reRootScaleSigma θ S (blkFam q) ≤ m0 :=
    fun q => reRootScaleSigma_le θ S (blkFam q)
  have hanti : Antitone fun q : ℚ => reRootScaleSigma θ S (blkFam q) :=
    antitone_reRootScaleSigma hmono
  have hcond := ReverseRationalAE.tendsto_condExp_iInf_rat_ae hle hanti hF
  have heq : ∀ᵐ ω ∂P, ∀ q : ℚ,
      blockAverageReal θ (blkFam q) F ω = P[F|reRootScaleSigma θ S (blkFam q)] ω :=
    ae_all_iff.2 fun q =>
      blockAverageReal_ae_eq_condExp_of_transport_gate (h q) hG (hblk q) hflow htr (h0 q) hFm hF
        hFs hFG
  filter_upwards [hcond, heq] with ω hω heqω
  simpa only [heqω] using hω

/-- The full-chain clause of `p:lem:timeconverge` for `F` vanishing off the gate. -/
theorem tendsto_setAverageReal_chain_ae_of_transport_gate [IsProbabilityMeasure P]
    (h : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q))
    (hmono : ∀ q q' : ℚ, q ≤ q' → ∀ ω : Ω, blkFam q ω 0 ⊆ blkFam q' ω 0)
    (hG : InvariantGate θ S G) (hblk : ∀ q : ℚ, ScaleCovariantBlocksOn G S (blkFam q))
    (hflow : FlowScaleIntertwine θ S) (htr : ParabolicTemporalTransport P θ S)
    (h0 : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < volume (blkFam q ω 0))
    (hFm : Measurable F) (hF : Integrable F P) (hFs : ScaleInvariant S F)
    (hFG : ∀ ω : Ω, ω ∉ G → F ω = 0)
    {chain : Ω → ℕ → ℚ} (hchain : ∀ ω : Ω, Tendsto (chain ω) atTop atTop)
    {anc : ℕ → Ω → Set ℝ} (hsel : ∀ (n : ℕ) (ω : Ω), anc n ω = blkFam (chain ω n) ω 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => setAverageReal θ (anc n ω) F ω) atTop
      (𝓝 (P[F|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)] ω)) := by
  filter_upwards [tendsto_blockAverageReal_ae_of_transport_gate h hmono hG hblk hflow htr h0 hFm
    hF hFs hFG] with ω hω
  have hrw : (fun n : ℕ => setAverageReal θ (anc n ω) F ω)
      = fun n : ℕ => blockAverageReal θ (blkFam (chain ω n)) F ω := by
    funext n
    rw [hsel n ω]
    rfl
  rw [hrw]
  exact hω.comp (hchain ω)

/-- **THE TRANSFER.**  The full-chain clause of `p:lem:timeconverge` for EVERY integrable
scale-invariant `F`, with the blocks covariant only on a conull invariant gate.  The conclusion is
character for character that of the ungated
`ScaledConditionalTemporalAveraging.tendsto_setAverageReal_chain_ae_of_transport`.

Proof: run the chain for `1_G · F` (which vanishes off `G`); `1_G · F = F` a.s., so the
conditional expectations agree a.s.; on `G` the flow never leaves `G`, so the averages agree. -/
theorem tendsto_setAverageReal_chain_ae_of_transport_gated [IsProbabilityMeasure P]
    (h : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q))
    (hmono : ∀ q q' : ℚ, q ≤ q' → ∀ ω : Ω, blkFam q ω 0 ⊆ blkFam q' ω 0)
    (hG : InvariantGate θ S G) (hGae : ∀ᵐ ω ∂P, ω ∈ G)
    (hblk : ∀ q : ℚ, ScaleCovariantBlocksOn G S (blkFam q))
    (hflow : FlowScaleIntertwine θ S) (htr : ParabolicTemporalTransport P θ S)
    (h0 : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < volume (blkFam q ω 0))
    (hFm : Measurable F) (hF : Integrable F P) (hFs : ScaleInvariant S F)
    {chain : Ω → ℕ → ℚ} (hchain : ∀ ω : Ω, Tendsto (chain ω) atTop atTop)
    {anc : ℕ → Ω → Set ℝ} (hsel : ∀ (n : ℕ) (ω : Ω), anc n ω = blkFam (chain ω n) ω 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => setAverageReal θ (anc n ω) F ω) atTop
      (𝓝 (P[F|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)] ω)) := by
  have hGm : MeasurableSet G := hG.measurableSet
  have hbase := tendsto_setAverageReal_chain_ae_of_transport_gate (F := G.indicator F) h hmono hG
    hblk hflow htr h0 (hFm.indicator hGm) (hF.indicator hGm)
    (scaleInvariant_indicator hFs fun _ hC ω => hG.scale_mem_iff hC ω)
    (fun ω hω => Set.indicator_of_notMem hω F) hchain hsel
  have hae : G.indicator F =ᵐ[P] F := by
    filter_upwards [hGae] with ω hω
    exact Set.indicator_of_mem hω F
  have hce : P[G.indicator F|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)]
      =ᵐ[P] P[F|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)] := condExp_congr_ae hae
  filter_upwards [hbase, hce, hGae] with ω hω hceω hGω
  have hflowF : (fun t : ℝ => G.indicator F (θ t ω)) = fun t : ℝ => F (θ t ω) := by
    funext t
    exact Set.indicator_of_mem ((hG.flow_mem_iff t ω).2 hGω) F
  have hrw : (fun n : ℕ => setAverageReal θ (anc n ω) (G.indicator F) ω)
      = fun n : ℕ => setAverageReal θ (anc n ω) F ω := by
    funext n
    show (volume (anc n ω)).toReal⁻¹ * ∫ t in anc n ω, G.indicator F (θ t ω)
      = (volume (anc n ω)).toReal⁻¹ * ∫ t in anc n ω, F (θ t ω)
    rw [hflowF]
  rw [hrw, hceω] at hω
  exact hω

end Convergence

/-! ## 4. The gated structure -/

/-- **The temporal block system of the root dyadic chain with `blockScale` GATED.**

Identical to `ScaledRootChainSystem` except that the parabolic block covariance is required only
at points of `G` (`blockScaleOn`), where `G` is measurable, invariant under every `θ t` and every
positive `S C` (`gate`), and of full `P ⊗ ν` measure (`gate_ae`). -/
structure ScaledRootChainSystemOn {Ω : Type*} [MeasurableSpace Ω] (G : Set (Ω × Grid))
    (P : Measure Ω) (ν : Measure Grid) (θ S : ℝ → Ω × Grid → Ω × Grid)
    (blkFam : ℚ → Ω × Grid → ℝ → Set ℝ) (sel : Ω × Grid → ℕ → ℚ) : Prop where
  /-- Each parameter gives a covariant temporal block system. -/
  system : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q)
  /-- The origin blocks increase with the parameter. -/
  nested : ∀ q q' : ℚ, q ≤ q' → ∀ p : Ω × Grid, blkFam q p 0 ⊆ blkFam q' p 0
  /-- The flow intertwines with the parabolic scaling. -/
  flowScale : FlowScaleIntertwine θ S
  /-- Every block system is parabolically covariant ON THE GATE. -/
  blockScaleOn : ∀ q : ℚ, ScaleCovariantBlocksOn G S (blkFam q)
  /-- The degree `-2` temporal mass transport of the marked law (`p:lem:timeMTP`). -/
  transport : ParabolicTemporalTransport (P.prod ν) θ S
  /-- The selecting parameters tend to infinity along the chain. -/
  selection_tendsto : ∀ p : Ω × Grid, Tendsto (sel p) atTop atTop
  /-- The selected origin blocks are the root dyadic blocks of the grid. -/
  selection_root : ∀ (n : ℕ) (p : Ω × Grid), rootTimeBlock p.2 (n : ℤ) = blkFam (sel p n) p 0
  /-- The gate is measurable and invariant under the flow and the scaling. -/
  gate : InvariantGate θ S G
  /-- The gate has full measure for the marked law. -/
  gate_ae : ∀ᵐ p ∂(P.prod ν), p ∈ G
  /-- The origin block has positive length almost surely, at every parameter (the manuscript's
  blocks are defined at almost every time; the origin is a vertex time almost surely under the
  rooted law).  Added 2026-09-23 with the a.e.-time generalisation of `TemporalBlockSystem`. -/
  origin_pos : ∀ q : ℚ, ∀ᵐ p ∂(P.prod ν), 0 < volume (blkFam q p 0)

section Structure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Measure Grid}
  {θ S : ℝ → Ω × Grid → Ω × Grid} {blkFam : ℚ → Ω × Grid → ℝ → Set ℝ}
  {sel : Ω × Grid → ℕ → ℚ}

/-- **An environment-coordinate gate is an invariant gate** of the marked flow and scaling. -/
theorem invariantGate_fst_preimage {θΩ SΩ : ℝ → Ω → Ω}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    {G₀ : Set Ω} (hG₀ : MeasurableSet G₀) (hθG : ∀ t : ℝ, θΩ t ⁻¹' G₀ = G₀)
    (hSG : ∀ C : ℝ, 0 < C → SΩ C ⁻¹' G₀ = G₀) :
    InvariantGate θ S (Prod.fst ⁻¹' G₀) := by
  refine ⟨measurable_fst hG₀, fun t => ?_, fun C hC => ?_⟩
  · ext ⟨y, d⟩
    show (θ t (y, d)).1 ∈ G₀ ↔ y ∈ G₀
    rw [hθ]
    exact Set.ext_iff.1 (hθG t) y
  · ext ⟨y, d⟩
    show (S C (y, d)).1 ∈ G₀ ↔ y ∈ G₀
    rw [hS]
    exact Set.ext_iff.1 (hSG C hC) y

/-- A `P`-conull environment-coordinate gate is `P ⊗ ν`-conull. -/
theorem ae_mem_fst_preimage [SFinite ν] {G₀ : Set Ω} (h : ∀ᵐ y ∂P, y ∈ G₀) :
    ∀ᵐ p ∂(P.prod ν), p ∈ Prod.fst ⁻¹' G₀ :=
  Measure.quasiMeasurePreserving_fst.ae h

/-- **The gated structure from the handoff's gated block data**
(`FlowSpaceBlockSystem.GatedRootChainBlocks`, produced by
`gatedRootChainBlocks_of_localTimeScaleOn`), the flow facts, the transport, and an
environment-coordinate gate invariant under the unmarked flow and scaling and `P`-conull. -/
theorem scaledRootChainSystemOn_of_gatedRootChainBlocks [SFinite ν] {G₀ : Set Ω}
    (hblk : FlowSpaceBlockSystem.GatedRootChainBlocks G₀ θ S blkFam sel)
    (hflow : FlowScaleIntertwine θ S) (htr : ParabolicTemporalTransport (P.prod ν) θ S)
    {θΩ SΩ : ℝ → Ω → Ω}
    (hθ : ∀ (t : ℝ) (y : Ω) (d : Grid), θ t (y, d) = (θΩ t y, translate (timeVec t) d))
    (hS : ∀ (C : ℝ) (y : Ω) (d : Grid), S C (y, d) = (SΩ C y, gridScale C d))
    (hG₀ : MeasurableSet G₀) (hθG : ∀ t : ℝ, θΩ t ⁻¹' G₀ = G₀)
    (hSG : ∀ C : ℝ, 0 < C → SΩ C ⁻¹' G₀ = G₀) (hae : ∀ᵐ y ∂P, y ∈ G₀)
    (h0 : ∀ q : ℚ, ∀ᵐ p ∂(P.prod ν), 0 < volume (blkFam q p 0)) :
    ScaledRootChainSystemOn (Prod.fst ⁻¹' G₀) P ν θ S blkFam sel where
  system := hblk.system
  nested := hblk.nested
  flowScale := hflow
  blockScaleOn := fun q C hC p hp s => hblk.blockScaleOn q C hC p hp s
  transport := htr
  selection_tendsto := hblk.selection_tendsto
  selection_root := hblk.selection_root
  gate := invariantGate_fst_preimage hθ hS hG₀ hθG hSG
  gate_ae := ae_mem_fst_preimage hae
  origin_pos := h0

end Structure

/-! ## 5. The consumers, gated (conclusions identical to `Limit/ScaledRootChainSystem`) -/

/-- Gated `ScaledRootChain.ae_ae_chain_of_transport`. -/
theorem ae_ae_chain_of_transport_gated {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D} [IsProbabilityMeasure ν]
    {θ S : ℝ → Ω × D → Ω × D} {blkFam : ℚ → Ω × D → ℝ → Set ℝ} {G : Set (Ω × D)}
    (hsys : ∀ q : ℚ, TemporalBlockSystem θ (blkFam q))
    (hnest : ∀ q q' : ℚ, q ≤ q' → ∀ p : Ω × D, blkFam q p 0 ⊆ blkFam q' p 0)
    (hflow : FlowScaleIntertwine θ S) (hG : InvariantGate θ S G)
    (hGae : ∀ᵐ p ∂(P.prod ν), p ∈ G) (hblk : ∀ q : ℚ, ScaleCovariantBlocksOn G S (blkFam q))
    (htr : ParabolicTemporalTransport (P.prod ν) θ S)
    (h0 : ∀ q : ℚ, ∀ᵐ p ∂(P.prod ν), 0 < volume (blkFam q p 0))
    {F₀ : Ω → ℝ} (hF₀m : Measurable F₀) (hF₀ : Integrable F₀ P)
    (hF₀s : ∀ C : ℝ, 0 < C → ∀ p : Ω × D, F₀ (S C p).1 = F₀ p.1)
    {sel : Ω × D → ℕ → ℚ} (hsel : ∀ p : Ω × D, Tendsto (sel p) atTop atTop)
    {b : D → ℕ → Set ℝ}
    (hanc : ∀ (n : ℕ) (p : Ω × D), b p.2 n = blkFam (sel p n) p 0)
    {dens : Ω → ℝ → ℝ}
    (hunmarked : ∀ (t : ℝ) (ω : Ω) (d : D), F₀ (θ t (ω, d)).1 = dens ω t)
    (hmono : ∀ d : D, Monotone fun n : ℕ => volume (b d n))
    (hfin : ∀ (d : D) (n : ℕ), volume (b d n) ≠ ⊤)
    (hgrid : GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × D => F₀ p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)])) :
    ∀ᵐ ω ∂P, ∀ᵐ d ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ n : ℕ,
      ENNReal.ofReal R ≤ volume (b d n) →
        |setAvg (b d n) (dens ω) - ∫ x, F₀ x ∂P| ≤ η := by
  have hFprod : Integrable (fun p : Ω × D => F₀ p.1) (P.prod ν) :=
    (MeasureTheory.measurePreserving_fst (μ := P) (ν := ν)).integrable_comp_of_integrable hF₀
  have hFm : Measurable fun p : Ω × D => F₀ p.1 := hF₀m.comp measurable_fst
  have hFs : ScaleInvariant S fun p : Ω × D => F₀ p.1 := fun C hC p => hF₀s C hC p
  have hle : (⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)) ≤ Prod.instMeasurableSpace :=
    le_trans (iInf_le (fun r : ℚ => reRootScaleSigma θ S (blkFam r)) (0 : ℚ))
      (reRootScaleSigma_le θ S (blkFam 0))
  have hchain := tendsto_setAverageReal_chain_ae_of_transport_gated (P := P.prod ν)
    (F := fun p : Ω × D => F₀ p.1) (anc := fun (n : ℕ) (p : Ω × D) => b p.2 n)
    hsys hnest hG hGae hblk hflow htr h0 hFm hFprod hFs hsel hanc
  have hconst := ae_eq_const_of_gridAveragedConstant hle hF₀
    (EventuallyEq.refl _ ((P.prod ν)[fun p : Ω × D => F₀ p.1|
      ⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)])) hgrid
  have hlim : ∀ᵐ p ∂(P.prod ν),
      Tendsto (fun n : ℕ => setAvg (b p.2 n) (dens p.1)) atTop (𝓝 (∫ x, F₀ x ∂P)) := by
    filter_upwards [hchain, hconst] with p hp hcp
    have hdens : (fun t : ℝ => F₀ (θ t p).1) = dens p.1 := by
      funext t
      exact hunmarked t p.1 p.2
    have hrw : ∀ n : ℕ, setAverageReal θ (b p.2 n) (fun q : Ω × D => F₀ q.1) p
        = setAvg (b p.2 n) (dens p.1) := by
      intro n
      show setAvg (b p.2 n) (fun t : ℝ => F₀ (θ t p).1) = setAvg (b p.2 n) (dens p.1)
      rw [hdens]
    simpa only [hrw, hcp] using hp
  exact GridChainTailConstant.ae_ae_forall_long_block hmono hfin hlim

section Consumers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {θ S : ℝ → Ω × Grid → Ω × Grid} {blkFam : ℚ → Ω × Grid → ℝ → Set ℝ}
  {sel : Ω × Grid → ℕ → ℚ} {G : Set (Ω × Grid)}

/-- Gated `ScaledRootChain.ae_chain_rootTimeBlock_of_scaledSystem`. -/
theorem ae_chain_rootTimeBlock_of_scaledSystemOn {ν : Measure Grid} [IsProbabilityMeasure ν]
    (hsys : ScaledRootChainSystemOn G P ν θ S blkFam sel)
    {F₀ : Ω → ℝ} (hF₀m : Measurable F₀) (hF₀ : Integrable F₀ P)
    (hF₀s : ∀ C : ℝ, 0 < C → ∀ p : Ω × Grid, F₀ (S C p).1 = F₀ p.1) {dens : Ω → ℝ → ℝ}
    (hunmarked : ∀ (t : ℝ) (ω : Ω) (d : Grid), F₀ (θ t (ω, d)).1 = dens ω t)
    (hgrid : GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × Grid => F₀ p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)])) :
    ∀ᵐ ω ∂P, ∀ᵐ D ∂ν, ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ k : ℤ,
      ENNReal.ofReal R ≤ volume (rootTimeBlock D k) →
        |setAvg (rootTimeBlock D k) (dens ω) - ∫ x, F₀ x ∂P| ≤ η := by
  have h := ae_ae_chain_of_transport_gated
    (b := fun (D : Grid) (n : ℕ) => rootTimeBlock D (n : ℤ))
    hsys.system hsys.nested hsys.flowScale hsys.gate hsys.gate_ae hsys.blockScaleOn
    hsys.transport hsys.origin_pos hF₀m hF₀ hF₀s hsys.selection_tendsto hsys.selection_root
    hunmarked
    monotone_volume_rootTimeBlock (fun D n => volume_rootTimeBlock_ne_top D (n : ℤ)) hgrid
  filter_upwards [h] with ω hω
  filter_upwards [hω] with D hD
  exact chain_rootTimeBlock_of_nat hD

/-- Gated `ScaledRootChain.ae_rootBlockDensity_of_scaledSystem`. -/
theorem ae_rootBlockDensity_of_scaledSystemOn {ν : Measure Grid} [IsProbabilityMeasure ν]
    (hsys : ScaledRootChainSystemOn G P ν θ S blkFam sel)
    {F₀ : Ω → ℝ} {dens : Ω → ℝ → ℝ} (hF₀m : Measurable F₀) (hF₀ : Integrable F₀ P)
    (hF₀s : ∀ C : ℝ, 0 < C → ∀ p : Ω × Grid, F₀ (S C p).1 = F₀ p.1)
    (hunmarked : ∀ (t : ℝ) (ω : Ω) (d : Grid), F₀ (θ t (ω, d)).1 = dens ω t)
    (hnonneg : ∀ (ω : Ω) (t : ℝ), 0 ≤ dens ω t)
    (hloc : ∀ᵐ ω ∂P, LocallyIntegrable (dens ω) volume)
    (hgrid : GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × Grid => F₀ p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)])) :
    ∀ᵐ ω ∂P, RootBlockDensity ν (dens ω) (∫ x, F₀ x ∂P) := by
  have hchain := ae_chain_rootTimeBlock_of_scaledSystemOn hsys hF₀m hF₀ hF₀s hunmarked hgrid
  filter_upwards [hchain, hloc] with ω hω hlocω
  exact
    { nonneg := hnonneg ω
      intervalIntegrable := fun T _ => intervalIntegrable_of_locallyIntegrable hlocω 0 T
      integrableOn := fun D k => integrableOn_rootTimeBlock_of_locallyIntegrable hlocω D k
      chain := hω }

/-- Gated `ScaledRootChain.ae_hasRootBlockData_of_scaledSystem`. -/
theorem ae_hasRootBlockData_of_scaledSystemOn {ν : Measure Grid} [IsProbabilityMeasure ν]
    (hsys : ScaledRootChainSystemOn G P ν θ S blkFam sel)
    {F : Ω → ℝ} {dens : Ω → ℝ → ℝ} (hF : UnmarkedRootDensity P θ F dens)
    (hFs : ∀ C : ℝ, 0 < C → ∀ p : Ω × Grid, F (S C p).1 = F p.1)
    (hgrid : GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × Grid => F p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)]))
    (hgridTrunc : ∀ m : ℕ, GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × Grid => min (F p.1) (m : ℝ)|
        ⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)])) :
    ∀ᵐ ω ∂P, HasRootBlockData ν (dens ω) (∫ x, F x ∂P) := by
  have hdnn : ∀ (ω : Ω) (t : ℝ), 0 ≤ dens ω t := by
    intro ω t
    obtain ⟨d⟩ := nonempty_of_isProbabilityMeasure ν
    rw [← hF.unmarked t ω d]
    exact hF.nonneg _
  have hmain := ae_rootBlockDensity_of_scaledSystemOn hsys hF.measurable hF.integrable hFs
    hF.unmarked hdnn hF.locallyIntegrable hgrid
  have htrunc : ∀ᵐ ω ∂P, ∀ m : ℕ, RootBlockDensity ν (fun t : ℝ => min (dens ω t) (m : ℝ))
      (∫ x, min (F x) (m : ℝ) ∂P) := by
    refine ae_all_iff.2 fun m => ?_
    have hmeas : Measurable fun x : Ω => min (F x) (m : ℝ) := hF.measurable.min measurable_const
    have hint : Integrable (fun x : Ω => min (F x) (m : ℝ)) P := by
      refine hF.integrable.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF.nonneg x) (Nat.cast_nonneg m))]
      exact min_le_left _ _
    have hsc : ∀ C : ℝ, 0 < C → ∀ p : Ω × Grid,
        min (F (S C p).1) (m : ℝ) = min (F p.1) (m : ℝ) := by
      intro C hC p
      rw [hFs C hC p]
    have hunm : ∀ (t : ℝ) (ω : Ω) (d : Grid),
        min (F (θ t (ω, d)).1) (m : ℝ) = min (dens ω t) (m : ℝ) := by
      intro t ω d
      rw [hF.unmarked t ω d]
    have hloc : ∀ᵐ ω ∂P, LocallyIntegrable (fun t : ℝ => min (dens ω t) (m : ℝ)) volume := by
      filter_upwards [hF.locallyIntegrable] with ω hω
      refine hω.mono
        ((hω.aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      show ‖min (dens ω t) (m : ℝ)‖ ≤ ‖dens ω t‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_min (hdnn ω t) (Nat.cast_nonneg m)), abs_of_nonneg (hdnn ω t)]
      exact min_le_left _ _
    exact ae_rootBlockDensity_of_scaledSystemOn (F₀ := fun x : Ω => min (F x) (m : ℝ))
      (dens := fun (ω : Ω) (t : ℝ) => min (dens ω t) (m : ℝ)) hsys hmeas hint hsc hunm
      (fun ω t => le_min (hdnn ω t) (Nat.cast_nonneg m)) hloc (hgridTrunc m)
  have hlim : Tendsto (fun m : ℕ => ∫ x, min (F x) (m : ℝ) ∂P) atTop (𝓝 (∫ x, F x ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (F := fun (m : ℕ) (x : Ω) => min (F x) (m : ℝ)) (f := F) F
      (fun m => (hF.measurable.min measurable_const).aestronglyMeasurable)
      hF.integrable (fun m => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · show ‖min (F x) (m : ℝ)‖ ≤ F x
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF.nonneg x) (Nat.cast_nonneg m))]
      exact min_le_left _ _
    · refine tendsto_atTop_of_eventually_const (i₀ := ⌈F x⌉₊) fun m hm => ?_
      exact min_eq_left (le_trans (Nat.le_ceil (F x)) (by exact_mod_cast hm))
  filter_upwards [hmain, htrunc] with ω hω hωt
  refine ⟨hω, fun (K : ℝ) (t : ℝ) => min (dens ω t) (⌊K⌋₊ : ℝ),
    fun K : ℝ => ∫ x, min (F x) (⌊K⌋₊ : ℝ) ∂P, ?_, ?_, ?_, ?_⟩
  · intro K _ s
    exact min_le_left _ _
  · intro K hK s
    exact le_trans (min_le_right _ _) (Nat.floor_le hK.le)
  · intro K _
    exact hωt ⌊K⌋₊
  · exact hlim.comp tendsto_nat_floor_atTop

/-- Gated `ScaledRootChain.gridAveragedConstant_of_scaledRootChainSystem`: `GridAveragedConstant`
for the tail conditional expectation, from `p:lem:regeninvariant` and environment ergodicity. -/
theorem gridAveragedConstant_of_scaledRootChainSystemOn {ν : Measure Grid}
    (hlaw : UniformGridLaw ν) (hsys : ScaledRootChainSystemOn G P ν θ S blkFam sel)
    {θΩ : ℝ → Ω → Ω}
    (hθ : ∀ (t : ℝ) (ω : Ω) (d : Grid), θ t (ω, d) = (θΩ t ω, translate (timeVec t) d))
    {SΩ : ℝ → Ω → Ω}
    (hS : ∀ (C : ℝ) (ω : Ω) (d : Grid), S C (ω, d) = (SΩ C ω, gridScale C d))
    {F : Ω → ℝ} {dens : Ω → ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F P)
    (hunmarked : ∀ (t : ℝ) (ω : Ω) (d : Grid), F (θ t (ω, d)).1 = dens ω t)
    (hdensscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), dens (SΩ C ω) s = dens ω (s / C ^ 2))
    {νenv : Measure Code.Env} [IsProbabilityMeasure νenv]
    (herg : EnvironmentLaws.EnvironmentErgodic νenv) {envOf : Ω → Code.Env}
    (henv : Measurable envOf) (hmarg : P.map envOf ≪ νenv)
    (hregen : RegenerativeInvariance P θΩ SΩ envOf) :
    GridAveragedConstant P ν
      ((P.prod ν)[fun p : Ω × Grid => F p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)]) := by
  have : IsProbabilityMeasure ν := hlaw.1
  obtain ⟨d₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hFs : ScaleInvariant S fun p : Ω × Grid => F p.1 := fun C hC p =>
    scaleInvariant_of_densscale (hsys.system 0) hS hunmarked hdensscale d₀ C hC p
  -- the density along the flow is jointly measurable and covariant
  have hdensm : Measurable fun q : Ω × ℝ => dens q.1 q.2 := by
    have h1 : Measurable fun q : Ω × ℝ => θ q.2 (q.1, d₀) :=
      (hsys.system 0).measurable_flow.comp
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have h2 : (fun q : Ω × ℝ => dens q.1 q.2) = fun q : Ω × ℝ => F (θ q.2 (q.1, d₀)).1 := by
      funext q
      exact (hunmarked q.2 q.1 d₀).symm
    rw [h2]
    exact hFm.comp (measurable_fst.comp h1)
  have hdensflow : ∀ (t : ℝ) (ω : Ω) (s : ℝ), dens (θΩ t ω) s = dens ω (s + t) := by
    intro t ω s
    rw [← hunmarked s (θΩ t ω) (translate (timeVec t) d₀), ← hunmarked (s + t) ω d₀,
      ← (hsys.system 0).flow_add s t (ω, d₀), hθ t ω d₀]
  -- the tail limit is the invariant version almost surely
  have hle : (⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)) ≤ Prod.instMeasurableSpace :=
    le_trans (iInf_le (fun r : ℚ => reRootScaleSigma θ S (blkFam r)) (0 : ℚ))
      (reRootScaleSigma_le θ S (blkFam 0))
  have hFprod : Integrable (fun p : Ω × Grid => F p.1) (P.prod ν) :=
    (MeasureTheory.measurePreserving_fst (μ := P) (ν := ν)).integrable_comp_of_integrable hFi
  -- THE ONLY CHANGE: the gated chain lemma
  have hchain := tendsto_setAverageReal_chain_ae_of_transport_gated (P := P.prod ν)
    (F := fun p : Ω × Grid => F p.1)
    (anc := fun (n : ℕ) (p : Ω × Grid) => rootTimeBlock p.2 (n : ℤ))
    hsys.system hsys.nested hsys.gate hsys.gate_ae hsys.blockScaleOn hsys.flowScale
    hsys.transport hsys.origin_pos (hFm.comp measurable_fst) hFprod hFs hsys.selection_tendsto
    hsys.selection_root
  have hL : (P.prod ν)[fun p : Ω × Grid => F p.1|⨅ r : ℚ, reRootScaleSigma θ S (blkFam r)]
      =ᵐ[P.prod ν] fun p : Ω × Grid => chainLimsup (dens p.1) p.2 := by
    filter_upwards [hchain] with p hp
    have hdens : (fun t : ℝ => F (θ t p).1) = dens p.1 := by
      funext t
      exact hunmarked t p.1 p.2
    have hrw : ∀ n : ℕ, setAverageReal θ (rootTimeBlock p.2 (n : ℤ))
        (fun q : Ω × Grid => F q.1) p = setAvg (rootTimeBlock p.2 (n : ℤ)) (dens p.1) := by
      intro n
      show setAvg (rootTimeBlock p.2 (n : ℤ)) (fun t : ℝ => F (θ t p).1)
        = setAvg (rootTimeBlock p.2 (n : ℤ)) (dens p.1)
      rw [hdens]
    simp only [hrw] at hp
    exact (chainLimsup_eq_of_tendsto_nat hp).symm
  -- the grid maps preserve the law
  have hτ : ∀ t : ℝ, MeasurePreserving (translate (timeVec t)) ν ν := fun t =>
    ⟨measurable_translate_left _, map_translate_of_uniformGridLaw hlaw _⟩
  have hSg : ∀ C : ℝ, 0 < C → MeasurePreserving (gridScale C) ν ν := by
    intro C hC
    have hfun : gridScale C = dilate (C ^ 2) (pow_pos hC 2) := funext (gridScale_of_pos hC)
    rw [hfun]
    exact ⟨measurable_dilate _ _, map_dilate_of_uniformGridLaw hlaw _⟩
  refine gridAveragedConstant_condExp_of_regenerativeInvariance
    (τ := fun t => translate (timeVec t)) (Sg := gridScale) herg henv hmarg hτ hSg hregen
    (measurable_chainLimsup hdensm) hle hL ?_ ?_
  · -- re-rooting invariance, for almost every grid
    intro t ω
    filter_upwards [ae_rootExhausts hlaw] with d hd
    show chainLimsup (dens (θΩ t ω)) (translate (timeVec t) d) = chainLimsup (dens ω) d
    have hfun : dens (θΩ t ω) = fun s : ℝ => dens ω (s + timeVec t 0) := by
      funext s
      rw [hdensflow, timeVec_zero]
    rw [hfun]
    exact chainLimsup_translate hd (timeVec t) (dens ω)
  · -- scaling invariance, for every grid
    intro C hC ω
    refine Eventually.of_forall fun d => ?_
    show chainLimsup (dens (SΩ C ω)) (gridScale C d) = chainLimsup (dens ω) d
    have hfun : dens (SΩ C ω) = fun s : ℝ => dens ω (s / C ^ 2) := by
      funext s
      exact hdensscale C hC ω s
    rw [hfun, gridScale_of_pos hC]
    exact chainLimsup_dilate (pow_pos hC 2) d (dens ω)

/-- **Gated `ScaledRootChain.ae_hasRootBlockData_of_regenerativeInvariance_scaled`** — the only
producer the downstream bracket-LLN welds consume.  Conclusion identical. -/
theorem ae_hasRootBlockData_of_regenerativeInvariance_scaledOn {ν : Measure Grid}
    (hlaw : UniformGridLaw ν) (hsys : ScaledRootChainSystemOn G P ν θ S blkFam sel)
    {θΩ : ℝ → Ω → Ω}
    (hθ : ∀ (t : ℝ) (ω : Ω) (d : Grid), θ t (ω, d) = (θΩ t ω, translate (timeVec t) d))
    {SΩ : ℝ → Ω → Ω}
    (hS : ∀ (C : ℝ) (ω : Ω) (d : Grid), S C (ω, d) = (SΩ C ω, gridScale C d))
    {F : Ω → ℝ} {dens : Ω → ℝ → ℝ} (hF : UnmarkedRootDensity P θ F dens)
    (hdensscale : ∀ C : ℝ, 0 < C → ∀ (ω : Ω) (s : ℝ), dens (SΩ C ω) s = dens ω (s / C ^ 2))
    {νenv : Measure Code.Env} [IsProbabilityMeasure νenv]
    (herg : EnvironmentLaws.EnvironmentErgodic νenv) {envOf : Ω → Code.Env}
    (henv : Measurable envOf) (hmarg : P.map envOf ≪ νenv)
    (hregen : RegenerativeInvariance P θΩ SΩ envOf) :
    ∀ᵐ ω ∂P, HasRootBlockData ν (dens ω) (∫ x, F x ∂P) := by
  have : IsProbabilityMeasure ν := hlaw.1
  obtain ⟨d₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hFs := scaleInvariant_of_densscale (hsys.system 0) hS hF.unmarked hdensscale d₀
  refine ae_hasRootBlockData_of_scaledSystemOn hsys hF hFs
    (gridAveragedConstant_of_scaledRootChainSystemOn hlaw hsys hθ hS hF.measurable hF.integrable
      hF.unmarked hdensscale herg henv hmarg hregen) fun m => ?_
  refine gridAveragedConstant_of_scaledRootChainSystemOn (F := fun x : Ω => min (F x) (m : ℝ))
    (dens := fun (ω : Ω) (s : ℝ) => min (dens ω s) (m : ℝ)) hlaw hsys hθ hS
    (hF.measurable.min measurable_const) ?_ ?_ ?_ herg henv hmarg hregen
  · refine hF.integrable.mono' (hF.measurable.min measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    show ‖min (F x) (m : ℝ)‖ ≤ F x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF.nonneg x) (Nat.cast_nonneg m))]
    exact min_le_left _ _
  · intro t ω d
    show min (F (θ t (ω, d)).1) (m : ℝ) = min (dens ω t) (m : ℝ)
    rw [hF.unmarked t ω d]
  · intro C hC ω s
    show min (dens (SΩ C ω) s) (m : ℝ) = min (dens ω (s / C ^ 2)) (m : ℝ)
    rw [hdensscale C hC ω s]

end Consumers

end ReflectedGMS.ScaledRootChainGated
