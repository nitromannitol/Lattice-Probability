/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.FlowCodingFrontier at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowCodingKernel
import LatticeProb.Bonanno.ReflectedGMS.Process.FlowCodingPositionExtension
import LatticeProb.Bonanno.ReflectedGMS.Limit.FlowCodingDensity
import LatticeProb.Bonanno.ReflectedGMS.Limit.OriginRootedTransportObstruction
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalBracketLLNGates
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationKernel
import LatticeProb.Bonanno.ReflectedGMS.Limit.ExactHoldingMeshProducer
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicCylinderLaw

/-!
# Main theorem 2 at the bridge kernel `κF` on the càdlàg carrier, and its non-vacuity audit

The frontier theorems `DirectionalBracketLLNGatesCoding.reflectedInvarianceConclusions_validLaw_rootedKernel`
and `InvarianceMainTheoremRegeneration.reflectedInvarianceConclusions_validLaw_regenerationKernel`
were stated on the raw coding and are vacuous there
(`RegenerationRawCodingVacuity.dirForm_bracketDensity_eq_zero_of_raw`).  This module restates main
theorem 2 on the càdlàg carrier `FlowSpace = Env × FlowCoding`, at the bridge kernel
`FlowCodingKernel.flowKernel` (`κF`), with `θΩ := reRootFlow`, `SΩ := reScale`,
`dens := lineDensity Φ`, `Fdir := flowFdir Φ`.

## What is discharged

* the path read-off gate `PathOriginRootedFibre κF (lineDensity Φ) Φ e` at every environment of the
  gate whose origin cell exists (`pathOriginRootedFibre_flowKernel`), hence `ν`-a.e.
  (`ae_pathOriginRootedFibre_flowKernel`) — forward read-off for EVERY set of paths, reverse for
  measurable sets, density clause at EVERY configuration;
* `hθ`, `hS` (`rfl`), the flow fields of `TemporalBlockSystem` and `flowScale` of `hsys`, and the
  reduction of the marked transport to the unmarked one (`FlowSystemInputs.toScaledRootChainSystem`);
* `UnmarkedRootDensity.measurable/nonneg/unmarked` and `hdensscale` (pointwise, from
  `GradientCovariant`, `Limit/FlowCodingDensity`);
* the gate data exist from MTP + FE (`exists_flowKernel_gate`), and the annealed law does not
  depend on the conull gate chosen (`compProd_flowKernel_congr`).

## The restated frontier theorem

`reflectedInvarianceConclusions_validLaw_flowKernel`: main theorem 2 at its own law from MTP, (FE),
ergodicity and the named inputs
* `hsys : FlowSystemInputs (ν ⊗ₘ κF) blkFam sel` — the block fields of the root chain system and
  the UNMARKED degree `-2` transport `ParabolicTemporalTransport (ν ⊗ₘ κF) reRootFlow reScale`;
* `hregen : RegenerativeInvariance (ν ⊗ₘ κF) reRootFlow reScale Prod.fst`;
* per harmonic coordinate and direction: integrability of `flowFdir Φ ζ` and local integrability
  of `lineDensity Φ ζ ω` (the probabilistic clauses of `UnmarkedRootDensity`);
* the gate `G` with `hG`, `hwalk`, `hext`, `hGc` (satisfiable: `exists_flowKernel_gate`).

## Non-vacuity audit

* **The raw obstruction does not transfer** (`rawObstructionPremises_hold_on_carrier`): every
  premise the raw vacuity proof used — joint measurability of the flow, measurability of `Fdir`,
  the pointwise `unmarked` identity for a density that reads the CURRENT state — holds on the
  carrier, while its conclusion (`¬ Measurable` flow) is refuted by `measurable_gridFlow`.  The
  mechanism was a raw path coding a non-Borel set of times; on `CadlagPath` every level set of the
  density along a path is Borel (`measurableSet_lineDensity_levelSet`).
* **⚠ SEVENTH VACUITY TRAP, located** (`transport_forces_repDifference_flowKernel`, checked):
  `hsys.transport` at the ORIGIN-rooted law `ν ⊗ₘ κF` forces, almost surely, for a.e. time `t` in
  the first root-area window at which the walker sits at an active label `n` (root label `m`):
  `rootAt (decode e) (z e n - z e m) = some n` — the vector from the root cell's representative
  to the current cell's representative lies in the interior of the current cell.  For a
  translation-covariant representative field (`lexMinField`, the centroid) this is the lattice
  condition; it holds at the shifted square tiling and fails with positive probability at every
  environment law whose neighbouring cells are not translates of the root cell along the
  representative difference (argued, see the module docstring of
  `Limit/OriginRootedTransportObstruction`).  So the frontier theorem below is non-vacuous only for
  representative fields `z` that keep the origin inside the walker's cell (`z e (root) = 0`
  with `z e n ∈ int (cell n)`, transported uniformly — see the handoff), or after restating the
  consumer at the manuscript's cell-rooted encoding (tex:1350).

Nothing here certifies `hsys`, `hregen`, the integrability inputs, `p:lem:timeMTP`,
`p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowCodingFrontier

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients AreaClocks InvarianceMainStatement QuenchedFormulation RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel ReflectedGMS.DirectionalBracketLLNGates
open ReflectedGMS.DirectionalBracketLLNWeld ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.ScaledRootChain ReflectedGMS.DyadicApproximation
open ReflectedGMS.DyadicGridTranslation ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.RootBlockGridProbability ReflectedGMS.ScaledConditionalTemporalAveraging
open ReflectedGMS.ParabolicTransport ReflectedGMS.TemporalMassTransport
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid ReflectedGMS.FlowCodingLine
open ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingDensity
open ReflectedGMS.OriginRootedTransportObstruction ReflectedGMS.BracketTimeAverage

/-! ### 1. The path read-off of the carrier -/

/-- **The read-off of a configuration**: its label path decoded into vertices of `e`. -/
def readOff (e : Env) (y : FlowCoding) : Trajectory (Vertex e.val) :=
  fun t => labelVertex e (y.1.toFun t)

theorem measurable_readOff (e : Env) : Measurable (readOff e) := by
  refine measurable_pi_iff.2 fun t => ?_
  have h : Measurable ((labelVertex e) ∘ fun y : FlowCoding => y.1.toFun (t : ℝ)) :=
    (measurable_of_countable (labelVertex e)).comp
      ((CadlagPath.measurable_eval (t : ℝ)).comp measurable_fst)
  exact h

theorem labelVertex_toENatLabel_map (e : Env) (o : Option (Vertex e.val)) :
    labelVertex e (toENatLabel (o.map Subtype.val)) = o := by
  cases o with
  | none => exact labelVertex_top e
  | some v =>
    show labelVertex e ((v.val : ℕ) : ℕ∞) = some v
    rw [labelVertex_natCast, dif_pos v.property]

/-- On the good set the read-off of the built configuration IS the forward walk. -/
theorem readOff_build {z : CellField} {e : Env} {r : Vertex e.val}
    {ω : (areaFamily e).Ω × (areaFamily e).Ω} (h : ω ∈ goodSet z e r) :
    readOff e (build z e r ω) = (areaFamily e).trajectory ω.1 := by
  funext t
  show labelVertex e ((build z e r ω).1.toFun (t : ℝ)) = (areaFamily e).X t ω.1
  rw [build_label_of_nonneg h (NNReal.coe_nonneg t), Real.toNNReal_coe, labelVertex_toENatLabel_map]

/-- The density clause holds at EVERY configuration. -/
theorem lineDensity_eq_pathForwardDensity (Φ : CellField) (e : Env) (y : FlowCoding)
    (ζ : Fin 2 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    lineDensity Φ ζ (e, y) s = pathForwardDensity e Φ ζ (readOff e y) s := by
  show dirForm (MartingaleIngredients.stateBracketDensity (decode e) (Φ.at e)
      (labelVertex e (y.1.toFun s))) ζ =
    dirForm (MartingaleIngredients.stateBracketDensity (decode e) (Φ.at e)
      (labelVertex e (y.1.toFun ((Real.toNNReal s : ℝ≥0) : ℝ)))) ζ
  rw [Real.coe_toNNReal s hs]

/-! ### 2. The repaired gate at `κF` -/

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **The repaired origin-rooted fibre holds at `κF`** at every environment of the gate whose origin
cell exists. -/
theorem pathOriginRootedFibre_flowKernel (Φ : CellField) {e : Env} (he : e ∈ G)
    {root : Vertex e.val} (hroot : rootAt (decode e) 0 = some root) :
    PathOriginRootedFibre (flowKernel z G hG hwalk hext) (lineDensity Φ) Φ e := by
  intro hnt
  have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
  have hr : rootVertex hlive = root := Subtype.ext (rootLabel_of_some hroot)
  set P := (areaFamily e).P (rootVertex hlive) with hPdef
  have hae : ∀ E : Set (Trajectory (Vertex e.val)),
      build z e (rootVertex hlive) ⁻¹' (readOff e ⁻¹' E) =ᵐ[P.prod P]
        Prod.fst ⁻¹' ((areaFamily e).trajectory ⁻¹' E) := by
    intro E
    filter_upwards [ae_mem_goodSet hwalk hext hlive] with ω hω
    show (readOff e (build z e (rootVertex hlive) ω) ∈ E) = ((areaFamily e).trajectory ω.1 ∈ E)
    rw [readOff_build hω]
  refine ⟨exhaustion e, decode_connected e,
    environmentWalkData_of_areaClockReachesLevelZeroIndices e (exhaustion e) (decode_connected e)
      (areaClockReaches_exhaustion e (hwalk e he)),
    root, readOff e, hroot, ?_, ?_, ?_⟩
  · exact Eventually.of_forall fun y ζ s hs => lineDensity_eq_pathForwardDensity Φ e y ζ hs
  · intro E hE
    rw [flowKernel_apply, flowFibre_of_live hlive] at hE
    have h1 : (P.prod P) (build z e (rootVertex hlive) ⁻¹' (readOff e ⁻¹' E)) = 0 :=
      nonpos_iff_eq_zero.1 ((Measure.le_map_apply
        (measurable_build z e (rootVertex hlive)).aemeasurable _).trans hE.le)
    rw [measure_congr (hae E), prod_fst_preimage, hPdef, hr] at h1
    exact h1
  · intro E hEm hE
    rw [flowKernel_apply, flowFibre_of_live hlive,
      Measure.map_apply (measurable_build z e (rootVertex hlive)) (measurable_readOff e hEm),
      measure_congr (hae E), prod_fst_preimage, hPdef, hr]
    exact hE

/-- **The repaired gate holds `ν`-a.e. at `κF`.** -/
theorem ae_pathOriginRootedFibre_flowKernel (ν : Measure Env) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) (hGc : ν Gᶜ = 0) :
    ∀ᵐ e ∂ν, PathOriginRootedFibre (flowKernel z G hG hwalk hext) (lineDensity Φ) Φ e := by
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  filter_upwards [hGae, ae_exists_rootAt_eq_some ν Φ hΦ] with e he hr
  obtain ⟨root, hroot⟩ := hr
  exact pathOriginRootedFibre_flowKernel Φ he hroot

/-! ### 3. The gate: existence and independence -/

/-- The environments at which the kernel's gate clauses hold: admissible, and the representative
path extends càdlàg from every start. -/
def GoodEnv (z : CellField) (e : Env) : Prop :=
  EnvironmentAreaClockAdmissible e ∧ ∀ start : Vertex e.val,
    ∀ᵐ ω ∂(areaFamily e).P start, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v

/-- **The gate exists from MTP + FE**: a measurable conull set of admissible environments at which
(B3) holds. -/
theorem exists_flowKernel_gate (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (z : CellField)
    (hz : IsCellRepresentative z) :
    ∃ G : Set Env, MeasurableSet G ∧ ν Gᶜ = 0 ∧ (∀ e ∈ G, EnvironmentAreaClockAdmissible e) ∧
      ExtensionGate z G := by
  have hA : ∀ᵐ e ∂ν, GoodEnv z e := by
    filter_upwards [AreaClockAdmissibleDischarge.ae_environmentAreaClockAdmissible ν hmt hFE,
      FlowCodingPositionExtension.ae_exists_cadlag_extension_areaFamily ν hmt hFE z hz]
      with e h1 h2
    exact ⟨h1, h2 h1⟩
  have hsub : ∀ e ∈ (toMeasurable ν {e | ¬ GoodEnv z e})ᶜ, GoodEnv z e := by
    intro e he
    by_contra hn
    exact he (subset_toMeasurable _ _ hn)
  refine ⟨(toMeasurable ν {e | ¬ GoodEnv z e})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
    fun e he => (hsub e he).1, fun e h => (hsub e h.1).2 _⟩
  rw [compl_compl, measure_toMeasurable]
  exact ae_iff.1 hA

/-- At an environment of two gates the two bridge kernels agree. -/
theorem flowKernel_apply_eq_of_mem {G₁ G₂ : Set Env} {hG₁ : MeasurableSet G₁}
    {hG₂ : MeasurableSet G₂} {hwalk₁ : ∀ e ∈ G₁, EnvironmentAreaClockAdmissible e}
    {hwalk₂ : ∀ e ∈ G₂, EnvironmentAreaClockAdmissible e} {hext₁ : ExtensionGate z G₁}
    {hext₂ : ExtensionGate z G₂} {e : Env} (h₁ : e ∈ G₁) (h₂ : e ∈ G₂) :
    flowKernel z G₁ hG₁ hwalk₁ hext₁ e = flowKernel z G₂ hG₂ hwalk₂ hext₂ e := by
  rw [flowKernel_apply, flowKernel_apply]
  by_cases hr : (e.val.1 (rootLabel e)).isSome
  · rw [flowFibre_of_live (G := G₁) ⟨h₁, hr⟩, flowFibre_of_live (G := G₂) ⟨h₂, hr⟩]
    rfl
  · rw [flowFibre_of_not_live (G := G₁) fun h => hr h.2,
      flowFibre_of_not_live (G := G₂) fun h => hr h.2]

/-- **The annealed law does not depend on the conull gate**: every binder stated at `ν ⊗ₘ κF` is
the same statement for every admissible conull gate with (B3), e.g. the similarity-closed one. -/
theorem compProd_flowKernel_congr (ν : Measure Env) {G₁ G₂ : Set Env} (hG₁ : MeasurableSet G₁)
    (hG₂ : MeasurableSet G₂) (hwalk₁ : ∀ e ∈ G₁, EnvironmentAreaClockAdmissible e)
    (hwalk₂ : ∀ e ∈ G₂, EnvironmentAreaClockAdmissible e) (hext₁ : ExtensionGate z G₁)
    (hext₂ : ExtensionGate z G₂) (h₁ : ν G₁ᶜ = 0) (h₂ : ν G₂ᶜ = 0) :
    ν ⊗ₘ flowKernel z G₁ hG₁ hwalk₁ hext₁ = ν ⊗ₘ flowKernel z G₂ hG₂ hwalk₂ hext₂ := by
  refine Measure.compProd_congr ?_
  filter_upwards [(ae_iff.2 h₁ : ∀ᵐ e ∂ν, e ∈ G₁), (ae_iff.2 h₂ : ∀ᵐ e ∂ν, e ∈ G₂)]
    with e he₁ he₂
  exact flowKernel_apply_eq_of_mem he₁ he₂

/-! ### 4. The system inputs -/

/-! ### 5. The restated frontier theorem -/

/-! ### 6. Non-vacuity audit -/

/-- **The bridge kernel's annealed law is rooted and coupled**: almost surely the walker starts in
the origin cell and the position path reads the representative field at rational vertex times. -/
theorem ae_rootedAt_coupled_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hGc : ν Gᶜ = 0) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      RootedAt ω ∧ ω ∈ Coupled fun e n => z.value e n := by
  have hS : MeasurableSet {ω : FlowSpace | RootedAt ω ∧ ω ∈ Coupled fun e n => z.value e n} :=
    measurableSet_rootedAt.inter (measurableSet_coupled fun n => z.measurable_label n)
  refine Measure.ae_compProd_of_ae_ae hS ?_
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  filter_upwards [hGae, Spatial.ae_notMem_boundaryMask_of_massTransport ν hmt] with e he hm
  obtain ⟨root, hroot, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e)
    (decode_geometry e) hm
  have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
  have hr : rootVertex hlive = root := Subtype.ext (rootLabel_of_some hroot)
  have hSe : MeasurableSet {y : FlowCoding | ((e, y) : FlowSpace) ∈
      {ω : FlowSpace | RootedAt ω ∧ ω ∈ Coupled fun e n => z.value e n}} :=
    measurable_prodMk_left hS
  rw [flowKernel_apply, flowFibre_of_live hlive]
  refine (ae_map_iff (measurable_build z e _).aemeasurable hSe).2 ?_
  filter_upwards [ae_mem_goodSet hwalk hext hlive] with ω hω
  refine ⟨⟨root, hroot, ?_⟩, build_mem_coupled hω⟩
  rw [build_label_zero hω, hr]

end ReflectedGMS.FlowCodingFrontier
