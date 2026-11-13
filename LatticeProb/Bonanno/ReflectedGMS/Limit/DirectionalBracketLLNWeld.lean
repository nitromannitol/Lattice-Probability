/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DirectionalBracketLLNWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNAllStartsTransfer
import LatticeProb.Bonanno.ReflectedGMS.Limit.RescaledBracketLLNBridge
import LatticeProb.Bonanno.ReflectedGMS.Limit.ScaledRootChainSystem
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketLLNPolarizedWeld
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerativeInvarianceReduction
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import LatticeProb.Bonanno.ReflectedGMS.Limit.ActualThresholdArrayWalk
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.QuenchedFormulation
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainTheoremThreeAtoms
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockAdmissibleDischarge
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssembly

/-!
# The weld `UniformDirectionalBracketLLN ν` ⟸ the all-starts bracket LLN producer

`AnalyticPacketAssembly.UniformDirectionalBracketLLN ν` (one of the three open inputs of
`InvarianceMainTheoremThreeAtoms.reflectedInvarianceConclusions_validLaw_of_three_atoms`) asks,
for every harmonic coordinate `Φ`, for the directional bracket LLN at EVERY start with slope
`ηᵀ (meanCovariance ν Φ) η`.  The producer
`BracketLLNAllStarts.rescaledBracketLLN_dirBracket_allStarts` delivers it with slope
`ηᵀ (polarMatrix (∫ Fdir (1,0)) (∫ Fdir (0,1)) (∫ Fdir (1,1))) η`, the integrals against the
annealed law `νenv ⊗ₘ κ` of the regeneration lane, for a generic kernel `κ`.

## What is discharged here

* `νenv := ν`; `hmin` and `IsReflectedWalk` from `EnvironmentWalkData` (the consumer's gate).
* **The covariance identification** (`polarMatrix_integral_eq_meanCovariance`): once the fibre
  functional reads the rooted bracket density, `Fdir ζ (e, x) = ζᵀ Γ(𝓗_e, H₀) ζ` for
  `ν`-a.e. `e` and `κ e`-a.e. `x` (`RootedDirectionalFunctional`), the polarization matrix of the
  three annealed means IS `meanCovariance ν Φ` — no integrability of `Γ` is assumed (it is
  read off `hF.integrable` through the disintegration `Measure.integral_compProd`), symmetry of
  `Γ` gives the off-diagonal entry.  This is the manuscript's `Σ = 𝔼[Γ(𝓗, H₀)]`
  (tex:1562): the environment marginal of the annealed law is `ν`, and the functional is read
  at time `0`, where the rooted cell is `H₀`.  **No mass transport and no flow invariance
  enter** — only the flow identity `θ 0 = id` (`TemporalBlockSystem.flow_zero`).
* `RootedDirectionalFunctional ↔ RootTimeDensity` (`rootedDirectionalFunctional_iff_rootTimeDensity`):
  by `UnmarkedRootDensity.unmarked` at `t = 0`, the functional and the density at time `0`
  coincide pointwise.
* `RootTimeDensity` is PROVED from the density-identification clause
  `dens ζ (e,x) s = forwardDensity e D Φ ζ (π x) s` of the origin-rooted fibre
  (`rootTimeDensity_of_originRootedFibre`): the forward read-off is dominated by the quenched law
  at the ORIGIN cell `rootAt (decode e) 0`, which starts there almost surely
  (`Existence.ae_process_zero`), and `stateBracketDensity (some H₀) = rootedGamma … 0`.  The
  existence of an exhaustion with walk data comes from `ae_environmentWalkData` (MTP + FE).

## The root gate, and why `root := start` is VACUOUS

With `root := start`, `Mroot := M` the producer's absolute-continuity gate reads
`∀ s, κ e (π ⁻¹' s) = 0 → areaSampleLaw (decode e) D hG start s = 0` together with the density
clause at the same `π` (`StartRootedReadOff`).  `rootedDirForm_eq_of_startRooted` proves that
this pair, with `RootTimeDensity` (which the covariance identification needs), FORCES
`ζᵀ Γ(start) ζ = ζᵀ Γ(H₀) ζ` for every direction: the time-0 value of the fibre density is the
origin cell's, and the gate transfers that almost-sure statement to the walk from `start`, which
sits at `start` at time `0`.  So the start-rooted gate holds at most at starts whose bracket
density equals the origin's — false at the actual data (and the consumer quantifies over EVERY
start).  The all-starts producer exists precisely so that the gate is needed only at ONE root.

The gate is therefore stated with an EXISTENTIAL root (`RootReadOffGate`), in the weakest form
the consumer can meet (after the consumer's own `start`, `M`, `CanonicalBracket`): both the
start-rooted form (`rootReadOffGate_of_startRooted`) and the origin-rooted form
(`rootReadOffGate_of_originRootedFibre`) imply it.

## Remaining named inputs (all owned by the regeneration lane)

`hsys`, `hθ`, `hS`, `hregen` (the kernel `κ` and its flows), `herg` (the main theorem's own
`AmbientEnvironmentErgodic`), and per harmonic coordinate the density data
`DirectionalDensityData` = `hF`, `hdensscale`, `RootTimeDensity`, `∀ᵐ e, RootReadOffGate`
— or, discharging `RootTimeDensity`, `∀ᵐ e, OriginRootedFibre` (`directionalDensityData_of_originRootedFibre`).

Satisfiability: `RootedDirectionalFunctional` holds for the manuscript's functional itself
(`rootedDirectionalFunctional_canonical`); the origin cell exists a.s.
(`ae_exists_rootAt_eq_some`); both read-offs of `OriginRootedFibre` hold for EVERY set at the
independent-halves fibre `P.prod B` through `Prod.fst` (`prod_fst_preimage`).

⚠ **Every exhaustion.**  `RootReadOffGate`/`OriginRootedFibre` are quantified over EVERY
`(D, hG)` with walk data — inherited from the consumer's `∀ D` in `AeDirectionalBracketLLN`, not
introduced here.  `κ` is one kernel, so at an exhaustion other than the one the fibre is built
from, the read-off `π_D` must reproduce a `D`-sample from the fibre's path: this needs the forward
path law to be exhaustion-independent (uniqueness in law of the reflected walk) plus a coupling
read-off.  Main theorem 2's own conclusion (`QuenchedFormulation.environmentProcessConclusions_iff`)
needs only ONE exhaustion per environment, so restating the atom at the exhaustion chosen by
`ae_environmentWalkData` would remove this burden.

**This is an implication.**  Nothing here certifies `p:lem:regeninvariant`, `ScaledRootChainSystem`
at the actual annealed law, the kernel `κ`, `p:lem:bracketlimit`, or either main theorem.
-/

-- Merged from `ReflectedGMS/Limit/BracketLLNAllStarts.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_BracketLLNAllStarts

/-!
# The bracket law of large numbers at the walk from EVERY start (closing the START GAP)

`Limit/RescaledBracketLLNBridgeDisintegrated.rescaledBracketLLN_dirBracket_of_regenerativeInvariance_disintegrated`
gives `RescaledBracketLLN` for `νenv`-a.e. environment, but only at a quenched law `P` for which
the fibrewise reading-off `∀ s, κ e (π ⁻¹' s) = 0 → P s = 0` holds — the law started where the
fibre law is rooted.  The invariance assembly and
`Limit/ActualThresholdArrayWalk.harray_of_canonicalBracket_of_directionalLLN` quantify over every
start.  This module closes that gap.

## The route

At a good environment, apply the disintegrated weld at the **root** quenched law
`areaSampleLaw (decode e) D hG root` (where the reading-off holds): almost surely under it, each
entry of the bracket satisfies the real-scale locally uniform limit.  Evaluate at `t = 1`: this is
the Cesàro law of large numbers `A_ij(T)/T → Σ_ij` of the additive functional
`A_ij(T) = ∫₀ᵀ ρ_ij(X_s) ds` of the area-clock path (`tendsto_ratio_of_rescaled`).  Move it to
the law started at any `start` with `BracketLLNAllStartsTransfer.ae_tendsto_ratio_of_root`
(strong Markov at the hitting time of `root` + one-sided shift invariance), and re-expand it into
the rescaled form at every time (`tendsto_rescaled_of_ratio`), which feeds
`RescaledBracketLLNBridge.rescaledBracketLLN_of_ae_tendsto` through `ae_tendsto_dirBracket`.

`areaSampleLaw (decode e) D hG x` IS `(Existence.processFamily D hG (areaRate (decode e))).P x`,
`exponentialAreaPath` IS that family's process, and `ordinaryEdgeBracket … i j u ω` IS
`pathIntegral (ρ_ij) (trajectory ω) u` — all by `rfl` (`ordinaryEdgeBracket_eq_pathIntegral`).

## What the all-starts step costs (honest list)

* `hwalk` — `IsReflectedWalk` of the area-clock family.  It is a component of
  `QuenchedFormulation.EnvironmentWalkData e D hG`, which
  `Recurrence/AreaClockAdmissibleDischarge.ae_environmentWalkData` proves for a.e. environment
  from MTP + FE (for its own `D`, `hG`); the corollary `…_of_environmentWalkData` takes it in
  that form.
* `CanonicalBracket` at the root and at the start — only their local-integrability conjunct is
  used (`HasOrdinaryEdgeBracket`'s second field).  The consumer
  `harray_of_canonicalBracket_of_directionalLLN` already requires `CanonicalBracket` at the start;
  the weld already requires it at the root.
* **Nothing else.**  The bridge's free fixed-time measurability binder `hmeas` is **discharged**
  here at every start (`BracketLLNAllStartsTransfer.aestronglyMeasurable_pathIntegral`, from right
  regularity).  No connectivity or ergodicity enters the transfer.

The root is any vertex at which the weld's `hfwd` and fibrewise reading-off hold (at the actual
data, the origin cell); no identification of the root with a particular cell is used.

**This is an implication.**  Nothing here certifies `p:lem:regeninvariant`, environment
ergodicity, `ScaledRootChainSystem` at the actual annealed law, `p:lem:bracketlimit`,
`p:thm:areaclt`, `hinc`, `hlimit`, `hbracket`, or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology ProbabilityTheory

open scoped NNReal ENNReal

namespace ReflectedGMS.BracketLLNAllStarts

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.BracketTimeAverage ReflectedGMS.RootBlockGridProbability
open ReflectedGMS.BracketLLNRootChain ReflectedGMS.GridAveragedConstantReduction
open ReflectedGMS.GridAveragedInvariantVersion ReflectedGMS.ScaledRootChain
open ReflectedGMS.BracketLLNPolarizedWeld
open ReflectedGMS.MartingaleIngredients ReflectedGMS.MartingaleLimit
open ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.AreaClocks

universe u

/-! ### 1. One environment: from the root to every start -/

section OneEnvironment

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V]

/-- Local integrability of every bracket entry, in the `HasOrdinaryEdgeBracket` shape, gives
`LocallyIntegrablePath` of every entry along the area-clock family's trajectory. -/
theorem ae_locallyIntegrablePath_of_intervalIntegrable (F : IndexedCells V)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected) (z : V → Plane) (x : V)
    (hx : ∀ᵐ ω ∂areaSampleLaw F D hG x, ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => stateBracketDensity F z (exponentialAreaPath F D s.toNNReal ω) i j)
        volume 0 (t : ℝ))
    (i j : Fin 2) :
    ∀ᵐ ω ∂(Existence.processFamily D hG (areaRate F)).P x,
      LocallyIntegrablePath (fun o => stateBracketDensity F z o i j)
        ((Existence.processFamily D hG (areaRate F)).trajectory ω) := by
  filter_upwards [hx] with ω hω n
  have h := hω i j (n : ℝ≥0)
  rw [NNReal.coe_natCast] at h
  exact h

/-- **Fixed-time measurability of every bracket entry under every start** — the bridge's free
`hmeas` binder, discharged from `IsReflectedWalk` alone. -/
theorem aestronglyMeasurable_ordinaryEdgeBracket (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) {hmin : F.graph.EnergyMinimizer}
    (hwalk : IsReflectedWalk F.graph (areaRate F) hmin
      (Existence.processFamily D hG (areaRate F)))
    (z : V → Plane) (start : V) (i j : Fin 2) (u : ℝ≥0) :
    AEStronglyMeasurable (ordinaryEdgeBracket F z (exponentialAreaPath F D) i j u)
      (areaSampleLaw F D hG start) :=
  aestronglyMeasurable_pathIntegral hwalk (fun o => stateBracketDensity F z o i j) start (u : ℝ)

end OneEnvironment

/-! ### 2. The environment-level statement: every start, for almost every environment -/

/-- The local-integrability conjunct of `CanonicalBracket`, on the original sample space. -/
theorem ae_intervalIntegrable_of_canonicalBracket {e : Code.Env}
    [Nontrivial (Code.Vertex e.val)] {D : (Code.decode e).graph.Exhaustion}
    {Φ : EnvironmentFields.CellField}
    {P : Measure (Existence.Sample (Code.Vertex e.val))}
    {M : ℝ≥0 → Existence.Sample (Code.Vertex e.val) → Plane}
    (hM : InvarianceMainStatement.CanonicalBracket e D Φ P M) :
    ∀ᵐ ω ∂P, ∀ (i j : Fin 2) (t : ℝ≥0),
      IntervalIntegrable
        (fun s : ℝ => stateBracketDensity (Code.decode e) (Φ.at e)
          (exponentialAreaPath (Code.decode e) D s.toNNReal ω) i j) volume 0 (t : ℝ) := by
  have h : ∀ᵐ ω ∂P, _ := hM.2.1
  exact h.mono fun _ hω => hω.2

/-! ## Shape check: `harray` at the actual walk from EVERY start, for almost every environment

The walk hypothesis is taken in the form `QuenchedFormulation.EnvironmentWalkData e D hG`, which
`Recurrence/AreaClockAdmissibleDischarge.ae_environmentWalkData` supplies for a.e. environment.
The start is chosen after the good environment and the root, with no reading-off hypothesis at
the start. -/

end ReflectedGMS.BracketLLNAllStarts

end Merged_BracketLLNAllStarts

set_option autoImplicit false

open MeasureTheory Filter Set ProbabilityTheory

open scoped NNReal ENNReal

namespace ReflectedGMS.DirectionalBracketLLNWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients AreaClocks InvarianceMainStatement QuenchedFormulation RootDensities
open ReflectedWalk
open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.BracketTimeAverage ReflectedGMS.BracketLLNRootChain
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.GridAveragedInvariantVersion
open ReflectedGMS.ScaledRootChain
open ReflectedGMS.BracketLLNPolarizedWeld ReflectedGMS.MartingaleIngredients
open ReflectedGMS.ApproximateBracketCLT ReflectedGMS.RescaledBracketLLNBridge
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.BracketClausesScalarReduction

/-! ## 1. The mean covariance as a polarization matrix -/

/-- The rooted directional bracket density `ζᵀ Γ(𝓗_e, H₀) ζ` (zero on the boundary mask). -/
noncomputable def rootedDirForm (Φ : CellField) (ζ : Fin 2 → ℝ) (e : Env) : ℝ :=
  dirForm (rootedGamma (decode e) (Φ.at e) 0) ζ

theorem dirForm_diag_eq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    dirForm M (dirVec 1 1) = M 0 0 + M 0 1 + M 1 0 + M 1 1 := by
  rw [dirForm_dirVec]; ring

/-- **`meanCovariance ν Φ` is the polarization matrix of the three directional means**, as soon
as the three directional forms are integrable.  Symmetry of `Γ` (`rootedGamma_symm`) gives the
off-diagonal entries. -/
theorem meanCovariance_eq_polarMatrix (ν : Measure Env) (Φ : CellField)
    (h10 : Integrable (rootedDirForm Φ (dirVec 1 0)) ν)
    (h01 : Integrable (rootedDirForm Φ (dirVec 0 1)) ν)
    (h11 : Integrable (rootedDirForm Φ (dirVec 1 1)) ν) :
    meanCovariance ν Φ =
      polarMatrix (∫ e, rootedDirForm Φ (dirVec 1 0) e ∂ν)
        (∫ e, rootedDirForm Φ (dirVec 0 1) e ∂ν) (∫ e, rootedDirForm Φ (dirVec 1 1) e ∂ν) := by
  have h00e : ∀ e, rootedGamma (decode e) (Φ.at e) 0 0 0 = rootedDirForm Φ (dirVec 1 0) e :=
    fun e => (dirForm_dirVec_one_zero _).symm
  have h11e : ∀ e, rootedGamma (decode e) (Φ.at e) 0 1 1 = rootedDirForm Φ (dirVec 0 1) e :=
    fun e => (dirForm_dirVec_zero_one _).symm
  have h01e : ∀ e, rootedGamma (decode e) (Φ.at e) 0 0 1 =
      (rootedDirForm Φ (dirVec 1 1) e - rootedDirForm Φ (dirVec 1 0) e
        - rootedDirForm Φ (dirVec 0 1) e) / 2 := by
    intro e
    simp only [rootedDirForm, dirForm_diag_eq, dirForm_dirVec_one_zero, dirForm_dirVec_zero_one]
    rw [InvarianceAssembly.rootedGamma_symm (decode e) (Φ.at e) 0 1 0]
    ring
  have hoff : meanCovariance ν Φ 0 1 =
      (∫ e, rootedDirForm Φ (dirVec 1 1) e ∂ν - ∫ e, rootedDirForm Φ (dirVec 1 0) e ∂ν
        - ∫ e, rootedDirForm Φ (dirVec 0 1) e ∂ν) / 2 := by
    show ∫ e, rootedGamma (decode e) (Φ.at e) 0 0 1 ∂ν = _
    rw [show (fun e => rootedGamma (decode e) (Φ.at e) 0 0 1) = fun e =>
        (rootedDirForm Φ (dirVec 1 1) e - rootedDirForm Φ (dirVec 1 0) e
          - rootedDirForm Φ (dirVec 0 1) e) / 2 from funext h01e]
    have hsub := integral_sub (h11.sub h10) h01
    simp only [Pi.sub_apply] at hsub
    rw [integral_div, hsub, integral_sub h11 h10]
  refine Matrix.ext fun i j => ?_
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [polarMatrix_zero_zero]
    exact integral_congr_ae (Eventually.of_forall h00e)
  · rw [polarMatrix_zero_one, hoff]
  · rw [polarMatrix_one_zero, InvarianceAssembly.meanCovariance_symm, hoff]
  · rw [polarMatrix_one_one]
    exact integral_congr_ae (Eventually.of_forall h11e)

/-! ## 2. Disintegrating an annealed mean whose fibres are constant -/

/-- If an integrable `f` on `ν ⊗ₘ κ` is, fibrewise almost surely, the environment function `g`,
then `g` is integrable and the annealed mean of `f` is the `ν`-mean of `g`. -/
theorem integrable_and_integral_eq_of_ae_fibre_eq {X : Type*} [MeasurableSpace X]
    {ν : Measure Env} [IsProbabilityMeasure ν] {κ : Kernel Env X} [IsMarkovKernel κ]
    {f : Env × X → ℝ} {g : Env → ℝ} (hf : Integrable f (ν ⊗ₘ κ))
    (hfg : ∀ᵐ e ∂ν, ∀ᵐ x ∂κ e, f (e, x) = g e) :
    Integrable g ν ∧ ∫ y, f y ∂(ν ⊗ₘ κ) = ∫ e, g e ∂ν := by
  have hfib : ∀ᵐ e ∂ν, ∫ x, f (e, x) ∂κ e = g e := by
    filter_upwards [hfg] with e he
    rw [integral_congr_ae he, integral_const]
    simp
  have hint : Integrable (fun e => ∫ x, f (e, x) ∂κ e) ν := by
    have h' : Integrable f ((Kernel.const Unit ν ⊗ₖ Kernel.prodMkLeft Unit κ) ()) := hf
    simpa using h'.integral_compProd
  exact ⟨hint.congr hfib, (Measure.integral_compProd hf).trans (integral_congr_ae hfib)⟩

/-! ## 3. The covariance identification -/

/-- **The fibre functional reads the rooted bracket density** — the manuscript's choice
(tex:1562: "the entries of `Γ` are unmarked functions of the current rooted cell"), gated
`ν`-a.e. and fibrewise `κ e`-a.e. -/
def RootedDirectionalFunctional {X : Type*} [MeasurableSpace X] (ν : Measure Env)
    (κ : Kernel Env X) (Φ : CellField) (Fdir : (Fin 2 → ℝ) → Env × X → ℝ) : Prop :=
  ∀ᵐ e ∂ν, ∀ᵐ x ∂κ e, ∀ ζ : Fin 2 → ℝ, Fdir ζ (e, x) = rootedDirForm Φ ζ e

/-- **The fibre density at time `0` is the origin cell's bracket density.** -/
def RootTimeDensity {X : Type*} [MeasurableSpace X] (ν : Measure Env)
    (κ : Kernel Env X) (Φ : CellField) (dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ) : Prop :=
  ∀ᵐ e ∂ν, ∀ᵐ x ∂κ e, ∀ ζ : Fin 2 → ℝ, dens ζ (e, x) 0 = rootedDirForm Φ ζ e

/-- **Satisfiability of the origin clause `rootAt (decode e) 0 = some root`**: for a harmonic
coordinate the origin is off the boundary mask almost surely, so the origin cell exists. -/
theorem ae_exists_rootAt_eq_some (ν : Measure Env) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∃ root : Vertex e.val, rootAt (decode e) 0 = some root := by
  filter_upwards [hΦ.2.2.2.2.1] with e he
  obtain ⟨v, hv, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) he.1
  exact ⟨v, hv⟩

/-- **The covariance identification.**  The producer's polarization matrix of the three
annealed means is `meanCovariance ν Φ`, from the integrability of the functional and its
identification with the rooted bracket density.  No integrability of `Γ` is assumed. -/
theorem polarMatrix_integral_eq_meanCovariance (ν : Measure Env) [IsProbabilityMeasure ν]
    (Φ : CellField) {X : Type*} [MeasurableSpace X] (κ : Kernel Env X) [IsMarkovKernel κ]
    {Fdir : (Fin 2 → ℝ) → Env × X → ℝ}
    (hint : ∀ ζ : Fin 2 → ℝ, Integrable (Fdir ζ) (ν ⊗ₘ κ))
    (hid : RootedDirectionalFunctional ν κ Φ Fdir) :
    polarMatrix (∫ y, Fdir (dirVec 1 0) y ∂(ν ⊗ₘ κ)) (∫ y, Fdir (dirVec 0 1) y ∂(ν ⊗ₘ κ))
        (∫ y, Fdir (dirVec 1 1) y ∂(ν ⊗ₘ κ)) = meanCovariance ν Φ := by
  have key : ∀ ζ : Fin 2 → ℝ, Integrable (rootedDirForm Φ ζ) ν ∧
      ∫ y, Fdir ζ y ∂(ν ⊗ₘ κ) = ∫ e, rootedDirForm Φ ζ e ∂ν := fun ζ =>
    integrable_and_integral_eq_of_ae_fibre_eq (hint ζ)
      (hid.mono fun _ he => he.mono fun _ hx => hx ζ)
  rw [(key _).2, (key _).2, (key _).2,
    meanCovariance_eq_polarMatrix ν Φ (key _).1 (key _).1 (key _).1]

/-! ## 4. The root gates -/

section Gates

variable {X : Type*} [MeasurableSpace X]

variable {κ : Kernel Env X} {dens : (Fin 2 → ℝ) → Env × X → ℝ → ℝ} {Φ : CellField}

/-- Both read-offs of the origin-rooted fibre hold, for every set, at the independent-halves
realization `P.prod B` read through `Prod.fst` (satisfiability of the two absolute-continuity
clauses at the actual quenched law, whatever `P` is). -/
theorem prod_fst_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (B : Measure β) [IsProbabilityMeasure B] (s : Set α) :
    (P.prod B) (Prod.fst ⁻¹' s) = P s := by
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

end Gates

/-! ## 5. The weld -/

end ReflectedGMS.DirectionalBracketLLNWeld
