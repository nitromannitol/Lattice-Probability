/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CellRootedFrameInvariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedEncodingRepair
import LatticeProb.Bonanno.ReflectedGMS.Limit.FlowCodingFrontier
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowGateRootChainGate

/-!
# Frame invariance of the line density and the marginal transfer at the cell-rooted law (P1)

Packet P1 of `outputs/rooting-decision-handoff.2026-09-18.md`.  The rooting decision states only
`hsys.transport` and `hregen` at the cell-rooted law `Q := (ν ⊗ₘ κ).map cellRoot`; every other
input stays at `ν` / `ν ⊗ₘ κ`.  Since `Q`'s environment marginal is the area-biased Palm law
(singular to `ν`, not `MassTransport`), the clauses `hmarg : Q.map Prod.fst ≪ ν` of the
downstream consumers are replaced here by what they were used for.

(a) **Frame invariance of the density.**  `lineDensity_reFrame` / `flowFdir_reFrame`: for a
  gradient-covariant field the directional bracket density read along the label path is
  unchanged by every frame change `reFrame u` (the canonical relabelling at unit scale;
  `FlowCodingDensity.labelBracket_simLabel` at `s = 1`).  Hence `lineDensity_cellRoot`,
  `flowFdir_cellRoot`, and `integral_flowFdir_map_cellRoot` (`∫ Fdir dQ = ∫ Fdir d(ν ⊗ₘ κ)`).

(b) **Marginal / ergodicity / gate transfer.**  `(cellRoot ω).1 = translateEnv (ω.2.2 0) ω.1`
  EVERYWHERE (`cellRoot_fst`), so a similarity-invariant environment event has the same
  preimage under `cellRoot` (`preimage_cellRoot_fst_of_similarityInvariant`) and
  **`map_cellRoot_fst`**: `(Q.map Prod.fst) A = ν A` for every measurable similarity-invariant
  `A`, for every Markov kernel `κ` (no coupling / rootedness input is needed).  Consequences:
  `environmentErgodic_map_cellRoot_fst` (so the consumers' `herg` + `hmarg` pair is discharged at
  `νenv := Q.map Prod.fst` with `hmarg := AbsolutelyContinuous.rfl`),
  `ae_mem_flowGate_cellRootedLaw` / `ae_mem_markedFlowGate_cellRootedLaw` (the gate is conull at
  `Q` from MTP+FE at `ν`, by `preimage_rootMap_flowGate`), and
  `scaledRootChainSystemOn_markedFlowGate_cellRootedLaw` (the gated system at `Q` from the gated
  blocks and the unmarked transport at `Q`, with no `hmarg`).

(c) **`hloc` / integrability at `Q`.**  `measurableSet_locallyIntegrable_lineDensity` (the
  local-integrability event is MEASURABLE — needed, since the forward transfer of an a.e.
  property to a push-forward fails for non-measurable invariant properties), whence
  `ae_locallyIntegrable_lineDensity_map_cellRoot`; `integrable_flowFdir_map_cellRoot`,
  `integrable_flowFdir_cellRootedLaw` (from MTP and the harmonic coordinate at `ν`), and the
  assembled `unmarkedRootDensity_flowFdir_cellRootedLaw` with `hloc` still at `ν ⊗ₘ κF`.

No new hypothesis is introduced: every binder is an existing input of the frontier theorem
(`MassTransport ν`, `FiniteEnergyMoment ν`, `EnvironmentErgodic ν`, `ν Gᶜ = 0`,
`IsHarmonicCoordinate ν Φ`, `hloc` at `ν ⊗ₘ κF`) or a producer output (`hblk`, the transport at
`Q` from P2).

Nothing here certifies the transport or `hregen` at `Q`, `p:lem:timeMTP`, or either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/FlowCodingIntegrability.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_FlowCodingIntegrability

/-!
**⚠ VACUOUS/SUPERSEDED (2026-09-18):** the frontier
`reflectedInvarianceConclusions_validLaw_flowKernel_loc` is probably vacuous.  Its
`hsys : FlowSystemInputs` has POINTWISE block fields on all of `FlowSpace`: `blockScale` fails at
any scale-fixed point (`FlowSpaceBlockSystem.not_scaledRootChainSystem_of_scaleFixed`, checked), so
the pointwise system is false once one valid environment is `√2`-self-similar
(`not_scaledRootChainSystem_flowSpace_of_selfSimilar`; existence of such an environment is argued).
Its `transport` field at the ORIGIN-rooted law `ν ⊗ₘ κF` forces a lattice condition
(`OriginRootedTransportObstruction.ae_rootedAt_reRootFlow_of_transport`, checked;
`FlowCodingFrontier.transport_forces_repDifference_flowKernel`) that fails for non-lattice laws
(argued).  Superseded by the gated, cell-rooted frontier `Limit/CellRootedFrontier*`
(`CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier`,
`CellRootedFrontierOneInput.reflectedInvarianceConclusions_validLaw_of_hregen`).
`integrable_flowFdir_flowKernel` itself is unaffected.

# `UnmarkedRootDensity.integrable` at the bridge kernel is PROVED

Under the annealed law `ν ⊗ₘ κF` the walker starts in the origin cell almost surely
(`FlowCodingFrontier.ae_rootedAt_coupled_flowKernel`), so the root-time functional `flowFdir Φ ζ`
equals the rooted directional bracket `rootedDirForm Φ ζ` of the environment almost surely; the
latter is integrable from MTP and the finite specific energy clause of `IsHarmonicCoordinate`
(`InvarianceAssembly.integrableBracket_of_aestronglyMeasurable`).  Hence the frontier theorem's
density input reduces to the local integrability of the line density
(`reflectedInvarianceConclusions_validLaw_flowKernel_loc`).

Nothing here certifies `hsys`, `hregen`, the local integrability input or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowCodingIntegrability

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients InvarianceMainStatement RootDensities
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.DirectionalBracketLLNWeld
open ReflectedGMS.AnalyticPacketAssembly ReflectedGMS.BracketTimeAverage
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.DyadicApproximation
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.FlowCodingKernel
open ReflectedGMS.FlowCodingDensity ReflectedGMS.FlowCodingFrontier
open ReflectedGMS.OriginRootedTransportObstruction

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- On a rooted configuration the root-time functional is the rooted directional bracket. -/
theorem flowFdir_eq_rootedDirForm {Φ : CellField} {ζ : Fin 2 → ℝ} {ω : FlowSpace}
    (h : RootedAt ω) : flowFdir Φ ζ ω = rootedDirForm Φ ζ ω.1 := by
  obtain ⟨v, hv, hY⟩ := h
  show labelBracket Φ ζ ω.1 (ω.2.1.toFun 0) = dirForm (rootedGamma (decode ω.1) (Φ.at ω.1) 0) ζ
  rw [hY, labelBracket, labelVertex_natCast, dif_pos v.property,
    MartingaleIngredients.stateBracketDensity_some, rootedGamma, hv]
  rfl

/-- **`UnmarkedRootDensity.integrable` at the bridge kernel, PROVED** from MTP and the harmonic
coordinate's finite specific energy. -/
theorem integrable_flowFdir_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) (ζ : Fin 2 → ℝ)
    (hGc : ν Gᶜ = 0) :
    Integrable (flowFdir Φ ζ) (ν ⊗ₘ flowKernel z G hG hwalk hext) := by
  have hint : IntegrableBracket ν Φ :=
    InvarianceAssembly.integrableBracket_of_aestronglyMeasurable ν Φ
      (fun i j => RootedBracketMeasurability.aestronglyMeasurable_rootedGamma ν hmt Φ i j)
      hΦ.2.2.2.1
  have hR : Integrable (rootedDirForm Φ ζ) ν := by
    show Integrable (fun e : Env =>
      ∑ i : Fin 2, ∑ j : Fin 2, ζ i * rootedGamma (decode e) (Φ.at e) 0 i j * ζ j) ν
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      ((hint i j).const_mul (ζ i)).mul_const (ζ j)
  have hmap : (ν ⊗ₘ flowKernel z G hG hwalk hext).map Prod.fst = ν :=
    Measure.fst_compProd ν (flowKernel z G hG hwalk hext)
  rw [← hmap] at hR
  have hfst : Integrable (fun ω : FlowSpace => rootedDirForm Φ ζ ω.1)
      (ν ⊗ₘ flowKernel z G hG hwalk hext) :=
    hR.comp_measurable measurable_fst
  refine hfst.congr ?_
  filter_upwards [ae_rootedAt_coupled_flowKernel (hG := hG) (hwalk := hwalk) (hext := hext) ν hmt
    hGc] with ω hω
  exact (flowFdir_eq_rootedDirForm hω.1).symm

end ReflectedGMS.FlowCodingIntegrability

end Merged_FlowCodingIntegrability

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CellRootedFrameInvariance

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.FlowCodingKernel
open ReflectedGMS.FlowCodingDensity ReflectedGMS.FlowCodingIntegrability
open ReflectedGMS.CellRootedEncodingRepair
open ReflectedGMS.SimilarityClosedGateFlow ReflectedGMS.FlowGateRootChainGate
open ReflectedGMS.ScaledRootChainGated ReflectedGMS.ParabolicTransport
open ReflectedGMS.TemporalMassTransport ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.DyadicApproximation ReflectedGMS.ScaledRootChain ReflectedGMS.Spatial
open ReflectedGMS.TrajectoryCoding

/-! ### (a) Frame invariance of the line density -/

/-- **The line density is invariant under every frame change**, at every configuration and time,
for a gradient-covariant field. -/
theorem lineDensity_reFrame {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    (u : Plane) (ω : FlowSpace) (t : ℝ) :
    lineDensity Φ ζ (reFrame u ω) t = lineDensity Φ ζ ω t := by
  show labelBracket Φ ζ (translateEnv u ω.1) (liftLabel (simLabel 1 u one_pos ω.1) (ω.2.1.toFun t))
    = labelBracket Φ ζ ω.1 (ω.2.1.toFun t)
  exact labelBracket_simLabel hΦ ζ one_pos ω.1 _

/-- The root-time functional is frame invariant. -/
theorem flowFdir_reFrame {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    (u : Plane) (ω : FlowSpace) : flowFdir Φ ζ (reFrame u ω) = flowFdir Φ ζ ω :=
  lineDensity_reFrame hΦ ζ u ω 0

/-- **The line density of the cell-rooted encoding is the line density.** -/
theorem lineDensity_cellRoot {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    (ω : FlowSpace) : lineDensity Φ ζ (cellRoot ω) = lineDensity Φ ζ ω := by
  funext t
  rw [cellRoot_eq_reFrame]
  exact lineDensity_reFrame hΦ ζ _ ω t

theorem flowFdir_cellRoot {Φ : CellField} (hΦ : GradientCovariant Φ) (ζ : Fin 2 → ℝ)
    (ω : FlowSpace) : flowFdir Φ ζ (cellRoot ω) = flowFdir Φ ζ ω := by
  rw [cellRoot_eq_reFrame]
  exact flowFdir_reFrame hΦ ζ _ ω

/-- `∫ Fdir dQ = ∫ Fdir dμ` for the cell-rooted push-forward `Q = μ.map cellRoot`. -/
theorem integral_flowFdir_map_cellRoot {Φ : CellField} (hΦ : GradientCovariant Φ)
    (ζ : Fin 2 → ℝ) (μ : Measure FlowSpace) :
    ∫ ω, flowFdir Φ ζ ω ∂(μ.map cellRoot) = ∫ ω, flowFdir Φ ζ ω ∂μ := by
  rw [integral_map measurable_cellRoot.aemeasurable
    (measurable_flowFdir Φ ζ).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun ω => flowFdir_cellRoot hΦ ζ ω)

/-! ### (b) The environment marginal of the cell-rooted law on similarity-invariant events -/

/-- The environment of the cell-rooted encoding is the environment translated to the walker's
time-`0` position, at every configuration. -/
theorem cellRoot_fst (ω : FlowSpace) : (cellRoot ω).1 = translateEnv (ω.2.2.toFun 0) ω.1 := by
  rw [cellRoot_eq_reFrame]
  rfl

/-- A similarity-invariant environment event is `cellRoot`-saturated, everywhere. -/
theorem preimage_cellRoot_fst_of_similarityInvariant {A : Set Env} (hA : SimilarityInvariant A) :
    cellRoot ⁻¹' (Prod.fst ⁻¹' A) = Prod.fst ⁻¹' A := by
  ext ω
  show (cellRoot ω).1 ∈ A ↔ ω.1 ∈ A
  rw [cellRoot_fst]
  exact (hA 1 _ one_pos ω.1 _ (isSimilarity_translateEnv _ ω.1)).symm

/-- For every law `μ` on the carrier, the cell-rooted environment marginal agrees with the
original one on similarity-invariant measurable events. -/
theorem map_fst_map_cellRoot_apply (μ : Measure FlowSpace) {A : Set Env} (hAm : MeasurableSet A)
    (hA : SimilarityInvariant A) :
    ((μ.map cellRoot).map Prod.fst) A = (μ.map Prod.fst) A := by
  rw [Measure.map_apply measurable_fst hAm, Measure.map_apply measurable_cellRoot (measurable_fst hAm),
    preimage_cellRoot_fst_of_similarityInvariant hA, Measure.map_apply measurable_fst hAm]

/-- **P1(b): the environment marginal of `Q = (ν ⊗ₘ κ).map cellRoot` agrees with `ν` on every
measurable similarity-invariant event** (every Markov kernel `κ`, in particular `κF`). -/
theorem map_cellRoot_fst (ν : Measure Env) [IsProbabilityMeasure ν] (κ : Kernel Env FlowCoding)
    [IsMarkovKernel κ] {A : Set Env} (hAm : MeasurableSet A) (hA : SimilarityInvariant A) :
    (((ν ⊗ₘ κ).map cellRoot).map Prod.fst) A = ν A := by
  rw [map_fst_map_cellRoot_apply _ hAm hA]
  show (ν ⊗ₘ κ).fst A = ν A
  rw [Measure.fst_compProd ν κ]

/-- **Ergodicity transfers to the cell-rooted environment marginal.**  With it, the consumers'
pair `herg : EnvironmentErgodic νenv`, `hmarg : Q.map Prod.fst ≪ νenv` is discharged at
`νenv := Q.map Prod.fst`, `hmarg := Measure.AbsolutelyContinuous.rfl`. -/
theorem environmentErgodic_map_cellRoot_fst {ν : Measure Env} [IsProbabilityMeasure ν]
    (herg : EnvironmentErgodic ν) (κ : Kernel Env FlowCoding) [IsMarkovKernel κ] :
    EnvironmentErgodic (((ν ⊗ₘ κ).map cellRoot).map Prod.fst) := by
  intro A hAm hA
  rw [map_cellRoot_fst ν κ hAm hA]
  exact herg A hAm hA

/-! ### (c) Local integrability and integrability at the cell-rooted law -/

/-- The line density is jointly measurable in the configuration and the time. -/
theorem measurable_lineDensity_uncurry (Φ : CellField) (ζ : Fin 2 → ℝ) :
    Measurable fun q : FlowSpace × ℝ => lineDensity Φ ζ q.1 q.2 := by
  have hY : Measurable fun q : FlowSpace × ℝ => q.1.2.1.toFun q.2 :=
    CadlagPath.measurable_eval_uncurry.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have he : Measurable fun q : FlowSpace × ℝ => q.1.1 := measurable_fst.comp measurable_fst
  have h : Measurable ((fun p : Env × ℕ∞ => labelBracket Φ ζ p.1 p.2) ∘
      fun q : FlowSpace × ℝ => (q.1.1, q.1.2.1.toFun q.2)) :=
    (measurable_labelBracket Φ ζ).comp (he.prodMk hY)
  have heq : (fun q : FlowSpace × ℝ => lineDensity Φ ζ q.1 q.2) =
      (fun p : Env × ℕ∞ => labelBracket Φ ζ p.1 p.2) ∘
        fun q : FlowSpace × ℝ => (q.1.1, q.1.2.1.toFun q.2) := by
    funext q
    rfl
  rw [heq]
  exact h

/-- Local integrability on the line of a measurable function is finiteness of its `L¹` norm on
every `[-n, n]`. -/
theorem locallyIntegrable_iff_lintegral_Icc {f : ℝ → ℝ} (hf : Measurable f) :
    LocallyIntegrable f volume ↔ ∀ n : ℕ, ∫⁻ s in Icc (-(n : ℝ)) n, ‖f s‖ₑ < ∞ := by
  constructor
  · intro h n
    exact hasFiniteIntegral_iff_enorm.1 (h.integrableOn_isCompact isCompact_Icc).2
  · intro h x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨Icc (-(n : ℝ)) n, Icc_mem_nhds (abs_lt.1 hn).1 (abs_lt.1 hn).2,
      hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 (h n)⟩

/-- **The local-integrability event of the line density is measurable.** -/
theorem measurableSet_locallyIntegrable_lineDensity (Φ : CellField) (ζ : Fin 2 → ℝ) :
    MeasurableSet {ω : FlowSpace | LocallyIntegrable (lineDensity Φ ζ ω) volume} := by
  have hg := measurable_lineDensity_uncurry Φ ζ
  have hset : {ω : FlowSpace | LocallyIntegrable (lineDensity Φ ζ ω) volume} =
      ⋂ n : ℕ, {ω : FlowSpace | ∫⁻ s in Icc (-(n : ℝ)) n, ‖lineDensity Φ ζ ω s‖ₑ < ∞} := by
    ext ω
    have hω : Measurable (lineDensity Φ ζ ω) := by
      have h : Measurable ((fun q : FlowSpace × ℝ => lineDensity Φ ζ q.1 q.2) ∘ Prod.mk ω) :=
        hg.comp measurable_prodMk_left
      simpa only [Function.comp_def] using h
    rw [Set.mem_iInter]
    exact locallyIntegrable_iff_lintegral_Icc hω
  rw [hset]
  refine MeasurableSet.iInter fun n => ?_
  have hF : Measurable fun ω : FlowSpace =>
      ∫⁻ s in Icc (-(n : ℝ)) n, ‖lineDensity Φ ζ ω s‖ₑ := by
    have hge : Measurable fun q : FlowSpace × ℝ => ‖lineDensity Φ ζ q.1 q.2‖ₑ := hg.enorm
    have h := Measurable.lintegral_prod_right' (ν := volume.restrict (Icc (-(n : ℝ)) n)) hge
    dsimp only at h
    exact h
  exact measurableSet_lt hF measurable_const

/-- **`hloc` transfers to the cell-rooted push-forward** of any law. -/
theorem ae_locallyIntegrable_lineDensity_map_cellRoot {Φ : CellField} (hΦ : GradientCovariant Φ)
    (ζ : Fin 2 → ℝ) {μ : Measure FlowSpace}
    (h : ∀ᵐ ω ∂μ, LocallyIntegrable (lineDensity Φ ζ ω) volume) :
    ∀ᵐ ω ∂(μ.map cellRoot), LocallyIntegrable (lineDensity Φ ζ ω) volume := by
  rw [ae_map_iff measurable_cellRoot.aemeasurable (measurableSet_locallyIntegrable_lineDensity Φ ζ)]
  filter_upwards [h] with ω hω
  rwa [lineDensity_cellRoot hΦ ζ ω]

/-- Integrability of the root-time functional transfers to the cell-rooted push-forward. -/
theorem integrable_flowFdir_map_cellRoot {Φ : CellField} (hΦ : GradientCovariant Φ)
    (ζ : Fin 2 → ℝ) {μ : Measure FlowSpace} (h : Integrable (flowFdir Φ ζ) μ) :
    Integrable (flowFdir Φ ζ) (μ.map cellRoot) := by
  rw [integrable_map_measure (measurable_flowFdir Φ ζ).aestronglyMeasurable
    measurable_cellRoot.aemeasurable]
  have hc : flowFdir Φ ζ ∘ cellRoot = flowFdir Φ ζ := funext fun ω => flowFdir_cellRoot hΦ ζ ω
  rw [hc]
  exact h

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **`UnmarkedRootDensity.integrable` at the cell-rooted law**, from MTP and the harmonic
coordinate at `ν`. -/
theorem integrable_flowFdir_cellRootedLaw (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) (ζ : Fin 2 → ℝ)
    (hGc : ν Gᶜ = 0) :
    Integrable (flowFdir Φ ζ) ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot) :=
  integrable_flowFdir_map_cellRoot hΦ.1 ζ
    (integrable_flowFdir_flowKernel (hG := hG) (hwalk := hwalk) (hext := hext) ν hmt Φ hΦ ζ hGc)

/-- **The density input at the cell-rooted law**, with `hloc` still at `ν ⊗ₘ κF`. -/
theorem unmarkedRootDensity_flowFdir_cellRootedLaw (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) (ζ : Fin 2 → ℝ)
    (hGc : ν Gᶜ = 0)
    (hloc : ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      LocallyIntegrable (lineDensity Φ ζ ω) volume) :
    BracketLLNRootChain.UnmarkedRootDensity ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      gridFlow (flowFdir Φ ζ) (lineDensity Φ ζ) :=
  unmarkedRootDensity_flowFdir hΦ.1 ζ (integrable_flowFdir_cellRootedLaw ν hmt Φ hΦ ζ hGc)
    (ae_locallyIntegrable_lineDensity_map_cellRoot hΦ.1 ζ hloc)

end ReflectedGMS.CellRootedFrameInvariance
