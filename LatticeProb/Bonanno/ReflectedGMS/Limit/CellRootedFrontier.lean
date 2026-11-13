/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CellRootedFrontier at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedFrameInvariance
import LatticeProb.Bonanno.ReflectedGMS.Limit.FlowCodingLocalIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceTimeScale
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTemporalTransport
import LatticeProb.Bonanno.ReflectedGMS.Temporal.HoldingDataFlowSpace
import LatticeProb.Bonanno.ReflectedGMS.Temporal.HoldingLawInputsCellRooted
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystemGated
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalBracketLLNGates
import LatticeProb.Bonanno.ReflectedGMS.Limit.ExactHoldingMeshProducer

/-!
# Main theorem 2 with the system and `hregen` at the CELL-ROOTED law (packet P4)

Packet P4 of `outputs/rooting-decision-handoff.2026-09-18.md` (rooting decision R2, light form).
Write `κF := FlowCodingKernel.flowKernel z G hG hwalk hext` and

  `Q := (validLaw P hP ⊗ₘ κF).map cellRoot`

(`Limit/CellRootedEncodingRepair.cellRoot`: the frame in which the walker's time-`0` position is the
origin).  Only the root-chain system (hence the temporal transport) and `hregen` are stated at `Q`;
the consumer, `hmt`, `hFE`, `herg`, the gate data and `hloc` stay at `ν := validLaw P hP` /
`ν ⊗ₘ κF`.

## The weld

The consumer (`DirectionalBracketLLNGated`) meets the root-chain system and `hregen` at exactly ONE
step: the `hdata` block (`HasRootBlockData` of the density, a.s., with the annealed mean as its
constant; `DirectionalBracketLLNGated` :341-345).  Everything after it (the disintegration to
`ν`-a.e. `e`, the fibre gate, the covariance identification) is law-local at `ν ⊗ₘ κF`.  So:

1. `ae_forall_ratio_limit_of_rootBlockData_pathReadOff` and
   `aeDirectionalBracketLLN_of_rootBlockData_pathGate`: the gated welds with the `hdata` block
   taken as a hypothesis (the rest verbatim; the time-`0` identification `Fdir = dens · 0` is a
   hypothesis instead of being read off `hsys.system 0`).
2. `ae_hasRootBlockData_flowKernel_of_cellRooted`: the `hdata` block is PRODUCED at `Q` by
   `ScaledRootChainGated.ae_hasRootBlockData_of_regenerativeInvariance_scaledOn` with
   `νenv := Q.map Prod.fst`, `hmarg := AbsolutelyContinuous.rfl`,
   `herg := environmentErgodic_map_cellRoot_fst herg κF` (P1: `Q`'s environment marginal is the
   Palm law, singular to `ν`, but it agrees with `ν` on similarity-invariant events) and the
   density data at `Q` (`unmarkedRootDensity_flowFdir_cellRootedLaw`, with `hloc` at `ν ⊗ₘ κF`);
   it is PULLED BACK to `ν ⊗ₘ κF` by `ae_of_ae_map` (always valid in this direction),
   `lineDensity_cellRoot` (frame invariance) and `integral_flowFdir_map_cellRoot`.
3. The gate `PathOriginRootedFibre` and `RootTimeDensity` stay at `ν`
   (`FlowCodingFrontier.ae_pathOriginRootedFibre_flowKernel`), integrability at `ν ⊗ₘ κF`
   (`FlowCodingIntegrability.integrable_flowFdir_flowKernel`).

## The frontier theorems

* `reflectedInvarianceConclusions_validLaw_cellRooted`: the binders of
  `FlowCodingIntegrability.reflectedInvarianceConclusions_validLaw_flowKernel_loc` with `hsys`
  replaced by the GATED system `ScaledRootChainSystemOn markedFlowGate Q …` (any blocks and
  selection), `hregen` at `Q`, `hloc` unchanged at `ν ⊗ₘ κF`, plus `hz` (below).
* `reflectedInvarianceConclusions_validLaw_cellRooted_of_system`: the same with `hloc` DISCHARGED
  (`FlowCodingLocalIntegrability.ae_locallyIntegrable_lineDensity_flowKernel`, from MTP + FE + the
  harmonic coordinate).
* **`reflectedInvarianceConclusions_validLaw_cellRootedFrontier`** (the cleanest form): main
  theorem 2 from MTP, (FE), ergodicity, the gate data and exactly three named inputs —
  - `hplain : CellRootedPlainTransport (ν ⊗ₘ κF)` (packet P2's transport binder: the plain
    time-shift transport for frame-invariant kernels at `ν ⊗ₘ κF`, EQUIVALENT to
    `ParabolicTemporalTransport Q reRootFlow reScale` by
    `CellRootedTemporalTransport.parabolicTemporalTransport_map_cellRoot_iff`);
  - `hregen : RegenerativeInvariance Q reRootFlow reScale Prod.fst` (packet P3);
  - `hz : InteriorOffMask z.value ∧ RepTranslationCovariant z.value ∧ RepDilationCovariant z.value`
    (packet P5).
  The whole gated system at `Q` comes from `hplain`
  (`CellRootedTemporalTransport.scaledRootChainSystemOn_cellRooted_of_plainTransport`: block fields
  from the label-free spatial time scale, gate conull at `Q` from MTP + FE), and `hloc` is proved.

`hz` is not consumed by these proofs.  It is carried because the transport binder is only
satisfiable for such `z`: P2 (checked, `Temporal/CellRootedTemporalTransport`) argues that the
transport at `Q` FAILS for a merely interior-off-mask, non-covariant representative, and
`InteriorOffMask` is what makes the cell-rooted configuration rooted along the flow
(`CellRootedEncodingRepair.ae_rootedAt_reRootFlow_cellRootedLaw`).  Without `hz` the frontier
would be vacuous for the `z` it is used with.

Nothing here certifies the plain transport, `hregen` at `Q`, `hz` for a measurable `CellField`,
`p:lem:timeMTP`, `p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory Topology

open scoped NNReal ENNReal

namespace ReflectedGMS.CellRootedFrontier

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients AreaClocks InvarianceMainStatement QuenchedFormulation RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.BracketTimeAverage ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.ScaledRootChain
open ReflectedGMS.BracketLLNPolarizedWeld ReflectedGMS.MartingaleIngredients
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.BracketClausesScalarReduction ReflectedGMS.BracketLLNAllStarts
open ReflectedGMS.DirectionalBracketLLNWeld ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.DirectionalBracketLLNGates ReflectedGMS.ScaledRootChainGated
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingDensity
open ReflectedGMS.CellRootedEncodingRepair
open ReflectedGMS.FlowGateRootChainGate ReflectedGMS.ParabolicTransport

/-! ## 1. The gated welds with the `hdata` block as a hypothesis -/

/-- `DirectionalBracketLLNGated.ae_forall_ratio_limit_of_regeneration_pathReadOff_gated` with its
`hdata` block (the only step that meets the system and `hregen`) taken as a hypothesis, for
arbitrary constants `c`.  The rest of the proof is verbatim. -/
theorem ae_forall_ratio_limit_of_rootBlockData_pathReadOff
    (Φ : CellField) {νenv : Measure Env} [IsProbabilityMeasure νenv]
    {X : Type*} [MeasurableSpace X] (κ : Kernel Env X) [IsMarkovKernel κ]
    {dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ} (c : (Fin 2 → ℝ) → ℝ)
    (hdata : ∀ ζ : Fin 2 → ℝ, ∀ᵐ y ∂(νenv ⊗ₘ κ),
      HasRootBlockData ReflectedGMS.DyadicGridLaw.gridMeasure (dens ζ y) (c ζ)) :
    ∀ᵐ e ∂νenv, ∀ (D : (decode e).graph.Exhaustion)
      (P : Measure (Existence.Sample (Vertex e.val)))
      (π : X → Trajectory (Vertex e.val)),
      (∀ᵐ ω ∂P, ∀ (i j : Fin 2) (t : ℝ≥0),
        IntervalIntegrable (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
          (exponentialAreaPath (decode e) D s.toNNReal ω) i j) volume 0 (t : ℝ)) →
      (∀ᵐ x ∂κ e, ∀ (ζ : Fin 2 → ℝ) (s : ℝ), 0 ≤ s →
        dens ζ (e, x) s = pathForwardDensity e Φ ζ (π x) s) →
      (∀ E : Set (Trajectory (Vertex e.val)),
        κ e (π ⁻¹' E) = 0 → P (areaTrajectory (decode e) D ⁻¹' E) = 0) →
      ∀ᵐ ω ∂P, ∀ i j : Fin 2,
        Tendsto (fun T : ℝ => ordinaryEdgeBracket (decode e) (Φ.at e)
            (exponentialAreaPath (decode e) D) i j (Real.toNNReal T) ω / T) atTop
          (𝓝 (polarMatrix (c (dirVec 1 0)) (c (dirVec 0 1)) (c (dirVec 1 1)) i j)) := by
  have hlaw := ReflectedGMS.DyadicCylinderLaw.uniformGridLaw_gridMeasure
  have h10 := Measure.ae_ae_of_ae_compProd (hdata (dirVec 1 0))
  have h01 := Measure.ae_ae_of_ae_compProd (hdata (dirVec 0 1))
  have h11 := Measure.ae_ae_of_ae_compProd (hdata (dirVec 1 1))
  filter_upwards [h10, h01, h11] with e he10 he01 he11
  intro D P π hint hfwd hread
  have hκ : ∀ᵐ x ∂κ e, PathDirectionalCesaro e Φ (c (dirVec 1 0)) (c (dirVec 0 1))
      (c (dirVec 1 1)) (π x) := by
    filter_upwards [he10, he01, he11, hfwd] with x hx10 hx01 hx11 hx
    exact And.intro
      (tendsto_intervalAverage_of_hasRootBlockData_of_eqOn hlaw (hx (dirVec 1 0)) hx10)
      (And.intro
        (tendsto_intervalAverage_of_hasRootBlockData_of_eqOn hlaw (hx (dirVec 0 1)) hx01)
        (tendsto_intervalAverage_of_hasRootBlockData_of_eqOn hlaw (hx (dirVec 1 1)) hx11))
  have hP : ∀ᵐ ω ∂P, PathDirectionalCesaro e Φ (c (dirVec 1 0)) (c (dirVec 0 1))
      (c (dirVec 1 1)) (areaTrajectory (decode e) D ω) :=
    ae_comp_of_pathReadOff hread hκ
  have hint' : ∀ᵐ ω ∂P, ∀ (i j : Fin 2) (T : ℝ), 0 ≤ T → IntervalIntegrable
      (fun s : ℝ => stateBracketDensity (decode e) (Φ.at e)
        (exponentialAreaPath (decode e) D (Real.toNNReal s) ω) i j) volume 0 T := by
    filter_upwards [hint] with ω hω
    intro i j T hT
    have h := hω i j (Real.toNNReal T)
    rwa [Real.coe_toNNReal T hT] at h
  refine bracketLLN_of_directional (decode e) (Φ.at e) (exponentialAreaPath (decode e) D) P
    _ (polarMatrix_symm _ _ _) hint' ?_
  filter_upwards [hP] with ω hω
  obtain ⟨h1, h2, h3⟩ := hω
  refine ⟨?_, ?_, ?_⟩
  · rw [dirForm_polarMatrix_one_zero]
    exact h1
  · rw [dirForm_polarMatrix_zero_one]
    exact h2
  · rw [dirForm_polarMatrix_one_one]
    exact h3

/-- `DirectionalBracketLLNGated.aeDirectionalBracketLLN_of_pathGate_gated` with the `hdata` block
as a hypothesis.  The system is no longer needed at all: its only other use was the time-`0`
identification `Fdir ζ y = dens ζ y 0` (`hFdens`). -/
theorem aeDirectionalBracketLLN_of_rootBlockData_pathGate (ν : Measure Env)
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    {X : Type*} [MeasurableSpace X] (κ : Kernel Env X) [IsMarkovKernel κ]
    {Fdir : (Fin 2 → ℝ) → Env × X → ℝ} {dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ}
    (hFdens : ∀ (ζ : Fin 2 → ℝ) (y : Env × X), Fdir ζ y = dens ζ y 0)
    (hint : ∀ ζ : Fin 2 → ℝ, Integrable (Fdir ζ) (ν ⊗ₘ κ))
    (hdata : ∀ ζ : Fin 2 → ℝ, ∀ᵐ y ∂(ν ⊗ₘ κ),
      HasRootBlockData ReflectedGMS.DyadicGridLaw.gridMeasure (dens ζ y)
        (∫ y, Fdir ζ y ∂(ν ⊗ₘ κ)))
    (hroot0 : RootTimeDensity ν κ Φ dens)
    (hgate : ∀ᵐ e ∂ν, PathRootReadOffGate κ dens Φ e) :
    AeDirectionalBracketLLN ν Φ := by
  have hid : RootedDirectionalFunctional ν κ Φ Fdir :=
    hroot0.mono fun e he => he.mono fun x hx ζ => (hFdens ζ (e, x)).trans (hx ζ)
  have hcov := polarMatrix_integral_eq_meanCovariance ν Φ κ hint hid
  unfold AeDirectionalBracketLLN
  filter_upwards [ae_forall_ratio_limit_of_rootBlockData_pathReadOff Φ κ
      (fun ζ => ∫ y, Fdir ζ y ∂(ν ⊗ₘ κ)) hdata, hgate,
    CanonicalOccupationWeld.ae_intervalIntegrable_bracketDensity ν hmt hFE Φ hΦ]
    with e he hg hloc
  intro hnt D hG hdata start M hM η
  obtain ⟨D0, hG0, hdata0, root, π, hdens, hread⟩ := hg hnt
  have hint0 := hloc hnt D0 hG0 hdata0 root
  have hr0 := he D0 (areaSampleLaw (decode e) D0 hG0 root) π hint0 hdens hread
  obtain ⟨_, _, hwalk0, _⟩ := hdata0
  obtain ⟨_, hrate, hwalk, _⟩ := hdata
  rw [← hcov]
  exact rescaledBracketLLN_dirBracket_of_otherExhaustion (decode e) hrate hwalk0 hwalk (Φ.at e)
    _ root start hint0 hr0 (ae_intervalIntegrable_of_canonicalBracket hM) η

/-! ## 2. The `hdata` block: produced at the cell-rooted law, pulled back to `ν ⊗ₘ κF` -/

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **The `hdata` block at `ν ⊗ₘ κF` from the gated system and `hregen` at the cell-rooted law.**
Produced at `Q = (ν ⊗ₘ κF).map cellRoot` with `νenv := Q.map Prod.fst` (P1: ergodic, and
`hmarg` is `AbsolutelyContinuous.rfl`), then pulled back through `cellRoot`: the density is frame
invariant and so is the annealed mean. -/
theorem ae_hasRootBlockData_flowKernel_of_cellRooted (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (herg : EnvironmentErgodic ν) (hGc : ν Gᶜ = 0)
    {Gm : Set (FlowSpace × Grid)} {blkFam : ℚ → FlowSpace × Grid → ℝ → Set ℝ}
    {sel : FlowSpace × Grid → ℕ → ℚ}
    (hsys : ScaledRootChainSystemOn Gm ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      ReflectedGMS.DyadicGridLaw.gridMeasure gridFlow gridScaleFlow blkFam sel)
    (hregen : RegenerativeInvariance ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      reRootFlow reScale Prod.fst)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) (ζ : Fin 2 → ℝ)
    (hloc : ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      LocallyIntegrable (lineDensity Φ ζ ω) volume) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      HasRootBlockData ReflectedGMS.DyadicGridLaw.gridMeasure (lineDensity Φ ζ ω)
        (∫ y, flowFdir Φ ζ y ∂(ν ⊗ₘ flowKernel z G hG hwalk hext)) := by
  -- `IsProbabilityMeasure` of both push-forwards is mathlib's unconditional `map` instance
  have hQ := ae_hasRootBlockData_of_regenerativeInvariance_scaledOn
    ReflectedGMS.DyadicCylinderLaw.uniformGridLaw_gridMeasure hsys
    (fun t y d => gridFlow_apply t y d) (fun C y d => gridScaleFlow_apply C y d)
    (CellRootedFrameInvariance.unmarkedRootDensity_flowFdir_cellRootedLaw ν hmt Φ hΦ ζ hGc hloc)
    (fun C hC y s => lineDensity_reScale hΦ.1 ζ hC y s)
    (CellRootedFrameInvariance.environmentErgodic_map_cellRoot_fst herg
      (flowKernel z G hG hwalk hext))
    measurable_fst Measure.AbsolutelyContinuous.rfl hregen
  rw [CellRootedFrameInvariance.integral_flowFdir_map_cellRoot hΦ.1 ζ] at hQ
  filter_upwards [ae_of_ae_map measurable_cellRoot.aemeasurable hQ] with ω hω
  rwa [CellRootedFrameInvariance.lineDensity_cellRoot hΦ.1 ζ ω] at hω

/-- **`hlln` from the gated system and `hregen` at the cell-rooted law**, with the gate, the
root-time identification and integrability at `ν` / `ν ⊗ₘ κF`. -/
theorem uniformDirectionalBracketLLN_cellRooted (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (herg : EnvironmentErgodic ν)
    (hGc : ν Gᶜ = 0)
    {Gm : Set (FlowSpace × Grid)} {blkFam : ℚ → FlowSpace × Grid → ℝ → Set ℝ}
    {sel : FlowSpace × Grid → ℕ → ℚ}
    (hsys : ScaledRootChainSystemOn Gm ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      ReflectedGMS.DyadicGridLaw.gridMeasure gridFlow gridScaleFlow blkFam sel)
    (hregen : RegenerativeInvariance ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      reRootFlow reScale Prod.fst)
    (hloc : ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → ∀ ζ : Fin 2 → ℝ,
      ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
        LocallyIntegrable (lineDensity Φ ζ ω) volume) :
    UniformDirectionalBracketLLN ν := by
  intro Φ hΦ
  have hgate := FlowCodingFrontier.ae_pathOriginRootedFibre_flowKernel (hG := hG) (hwalk := hwalk)
    (hext := hext) ν Φ hΦ hGc
  exact aeDirectionalBracketLLN_of_rootBlockData_pathGate ν hmt hFE Φ hΦ
    (flowKernel z G hG hwalk hext) (Fdir := flowFdir Φ) (dens := lineDensity Φ)
    (fun _ _ => rfl)
    (fun ζ => FlowCodingIntegrability.integrable_flowFdir_flowKernel (hG := hG) (hwalk := hwalk)
      (hext := hext) ν hmt Φ hΦ ζ hGc)
    (fun ζ => ae_hasRootBlockData_flowKernel_of_cellRooted ν hmt herg hGc hsys hregen Φ hΦ ζ
      (hloc Φ hΦ ζ))
    (rootTimeDensity_of_pathOriginRootedFibre ν hgate)
    (hgate.mono fun _ h => pathRootReadOffGate_of_pathOriginRootedFibre h)

/-! ## 3. Main theorem 2 at its own law -/

set_option linter.unusedVariables false in
/-- **Main theorem 2 at its own law with the GATED system and `hregen` at the cell-rooted law**
`Q := (validLaw P hP ⊗ₘ κF).map cellRoot`: the binders of
`FlowCodingIntegrability.reflectedInvarianceConclusions_validLaw_flowKernel_loc` except `hsys`
(now `ScaledRootChainSystemOn markedFlowGate Q …`) and `hregen` (now at `Q`), plus `hz` (not
consumed; see the module docstring). -/
theorem reflectedInvarianceConclusions_validLaw_cellRooted
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (herg : AmbientEnvironmentErgodic P hP)
    (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hGc : validLaw P hP Gᶜ = 0)
    {Gm : Set (FlowSpace × Grid)}
    {blkFam : ℚ → FlowSpace × Grid → ℝ → Set ℝ} {sel : FlowSpace × Grid → ℕ → ℚ}
    (hsys : ScaledRootChainSystemOn Gm
      ((validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      ReflectedGMS.DyadicGridLaw.gridMeasure gridFlow gridScaleFlow blkFam sel)
    (hregen : RegenerativeInvariance ((validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      reRootFlow reScale Prod.fst)
    (hloc : ∀ Φ : CellField, IsHarmonicCoordinate (validLaw P hP) Φ → ∀ ζ : Fin 2 → ℝ,
      ∀ᵐ ω ∂(validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext),
        LocallyIntegrable (lineDensity Φ ζ ω) volume)
    (hz : InteriorOffMask z.value ∧ RepTranslationCovariant z.value ∧
      RepDilationCovariant z.value) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  ExactHoldingMeshProducer.reflectedInvarianceConclusions_validLaw_of_lln P hP hmt hFE
    (uniformDirectionalBracketLLN_cellRooted (validLaw P hP) hmt hFE herg hGc hsys hregen hloc)

/-- **The same with `hloc` DISCHARGED** (`FlowCodingLocalIntegrability`, from MTP + FE + the harmonic
coordinate): main theorem 2 from the gated system and `hregen` at the cell-rooted law, and `hz`. -/
theorem reflectedInvarianceConclusions_validLaw_cellRooted_of_system
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (herg : AmbientEnvironmentErgodic P hP)
    (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hGc : validLaw P hP Gᶜ = 0)
    {Gm : Set (FlowSpace × Grid)}
    {blkFam : ℚ → FlowSpace × Grid → ℝ → Set ℝ} {sel : FlowSpace × Grid → ℕ → ℚ}
    (hsys : ScaledRootChainSystemOn Gm
      ((validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      ReflectedGMS.DyadicGridLaw.gridMeasure gridFlow gridScaleFlow blkFam sel)
    (hregen : RegenerativeInvariance ((validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      reRootFlow reScale Prod.fst)
    (hz : InteriorOffMask z.value ∧ RepTranslationCovariant z.value ∧
      RepDilationCovariant z.value) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  reflectedInvarianceConclusions_validLaw_cellRooted P hP hmt hFE herg z G hG hwalk hext hGc hsys
    hregen
    (fun Φ hΦ ζ => FlowCodingLocalIntegrability.ae_locallyIntegrable_lineDensity_flowKernel
      (validLaw P hP) hmt hFE Φ hΦ ζ hGc)
    hz

/-- **The frontier in its cleanest form.**  Main theorem 2 at its own law from MTP, (FE),
ergodicity, the gate data (`G`, `hG`, `hwalk`, `hext`, `hGc`; satisfiable by
`FlowCodingFrontier.exists_flowKernel_gate`) and exactly three named inputs:

* `hplain` — `CellRootedPlainTransport (ν ⊗ₘ κF)`, the plain time-shift transport for
  frame-invariant kernels (packet P2; equivalent to the unmarked transport at `Q`,
  `CellRootedTemporalTransport.parabolicTemporalTransport_map_cellRoot_iff`);
* `hregen` — `RegenerativeInvariance Q reRootFlow reScale Prod.fst` (packet P3);
* `hz` — `InteriorOffMask z.value ∧ RepTranslationCovariant z.value ∧ RepDilationCovariant z.value`
  (packet P5; carried for the satisfiability of `hplain`, not consumed here).

The gated root-chain system at `Q` comes from `hplain`
(`CellRootedTemporalTransport.scaledRootChainSystemOn_cellRooted_of_plainTransport`: block fields
and selection from the label-free spatial time scale, flow fields and `flowScale` by the grid
algebra, gate conull at `Q` from MTP + FE); `hloc` is proved
(`FlowCodingLocalIntegrability.ae_locallyIntegrable_lineDensity_flowKernel`). -/
theorem reflectedInvarianceConclusions_validLaw_cellRootedFrontier
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (herg : AmbientEnvironmentErgodic P hP)
    (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hGc : validLaw P hP Gᶜ = 0)
    (hplain : CellRootedTemporalTransport.CellRootedPlainTransport
      (validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext))
    (hregen : RegenerativeInvariance ((validLaw P hP ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      reRootFlow reScale Prod.fst)
    (hz : InteriorOffMask z.value ∧ RepTranslationCovariant z.value ∧
      RepDilationCovariant z.value) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  reflectedInvarianceConclusions_validLaw_cellRooted_of_system P hP hmt hFE herg z G hG hwalk hext
    hGc
    (HoldingDataFlowSpace.scaledRootChainSystemOn_cellRooted_of_plainTransport_holding hmt hFE z G hG
      hwalk hext hplain
      (HoldingLawInputsCellRooted.holdingLawInputs_cellRooted (validLaw P hP) hmt hGc))
    hregen hz

/-! ## 4. Joint satisfiability of `hz` and the gate data -/

/-- An interior-off-mask field is a cell representative. -/
theorem isCellRepresentative_of_interiorOffMask {z : CellField} (hz : InteriorOffMask z.value) :
    IsCellRepresentative z :=
  fun e v => (hz e v.val v.property).2

/-- **The gate data exist for every `z` with `hz`** (from MTP + FE at `ν`), so the gate binders of
the frontier theorems and `hz` are jointly satisfiable. -/
theorem exists_flowKernel_gate_of_interiorOffMask (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) {z : CellField}
    (hz : InteriorOffMask z.value) :
    ∃ G : Set Env, MeasurableSet G ∧ ν Gᶜ = 0 ∧ (∀ e ∈ G, EnvironmentAreaClockAdmissible e) ∧
      ExtensionGate z G :=
  FlowCodingFrontier.exists_flowKernel_gate ν hmt hFE z
    (isCellRepresentative_of_interiorOffMask hz)

end ReflectedGMS.CellRootedFrontier
