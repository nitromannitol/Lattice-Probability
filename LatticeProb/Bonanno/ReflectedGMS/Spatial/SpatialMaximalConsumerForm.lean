/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.SpatialMaximalConsumerForm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge

/-!
# `s:prop:maximal` in the exact form its consumers assume — the reduction to a marked space

The two consumers of manuscript Proposition `s:prop:maximal` in this project,

* `Spatial/AlmostSureSpatialDiameterBounds.ae_spatialDiameterCellBounds_of_ballBound`
  (corrector lane, rows `n = 1` and `n = 16`) and
* `Recurrence/QuenchedFormulation.ae_quenchedWalkConclusion_of_massTransport` /
  `Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` (recurrence lane),

carry the *same* hypothesis, verbatim:

`hMax : ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
  (∫⁻ x in B̄_r, ρ_FE(𝓗_e) x) ≤ ENNReal.ofReal (r ^ 2) * M`,

the quadratic maximal bound `M(ρ_FE) < ∞` of `s:prop:maximal` for the rooted (FE) density.
This module states that hypothesis as a **conclusion**, for an environment law `ν` on `Env`,
and reduces it to the third clause of `s:prop:maximal` on a *marked* configuration space
whose environment marginal is `ν`.

## The marked space over `ν`

The manuscript proves `s:prop:maximal` after attaching an independent uniform dyadic system
`𝔻'` and then says: *"This conclusion concerns `ω` alone, so the auxiliary `𝔻'` can be
integrated out."*  Here that integration is `ae_fst_of_ae_prod`.  In addition the marked
space is built over a **good set** `G` of environments — measurable, of full `ν`-measure and
stable under re-rooting — because the pathwise regularity of the origin dyadic chain that the
maximal inequality needs (`SpatialMaximalInequality.OriginChainRegular`) holds only almost
surely for the actual environment law, not for every code.  Passing to a full-measure set
costs nothing (`ae_of_ae_comap_subtype`) and is what makes the origin-chain regularity an
honest *pathwise* hypothesis on the good space.

`goodReRooting G hG : MarkedReRooting (G × Grid)` is the actual marked re-rooting of
`Spatial/ActualMarkedBlockTransport` restricted to `G`: the environment observable is the
inclusion, the grid observable is the second coordinate, and re-rooting at `w` is the canonical
similarity action at unit scale together with `DyadicGridTranslation.translate w`.  Its
re-rooting property `EnvReRooting` is a theorem (`envReRooting_goodReRooting`), exactly as on
the full space.

## What is proved and what is not

`ae_exists_ballBound_of_good_ballMaximal` is **conditional on one hypothesis and nothing
else beyond the choice of a good set**: `hmax`, the almost-sure finiteness of the manuscript's
maximal function `M(ρ_FE)` on the good marked space, i.e. the third clause of `s:prop:maximal`
for the functional `rootFE (goodReRooting G hG)`.  Neither this module nor anything it imports
proves that clause for the actual law; producing it is the remaining content of
`s:prop:maximal` (the dyadic block martingale), and this module does not certify it.

The generic form `ae_exists_ballBound_of_marked` records the reduction for an arbitrary marked
space `(Ω, μ, R)` with `EnvReRooting R`, given only the transfer of almost-sure statements
from `μ` along `R.env` to `ν` (`hproj`), which the product/subtype construction above supplies.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.SpatialMaximalConsumerForm

open Code EnvironmentLaws MarkedBlockAveraging SpatialMaximalInequality
open ActualSpatialDensityBridge ActualMarkedBlockTransport DyadicApproximation
open DyadicGridTranslation DyadicGridLaw

/-! ### Integrating out the marks and the good set -/

/-- **"The auxiliary `𝔻'` can be integrated out."**  An almost-sure statement about the first
coordinate under a product law is an almost-sure statement under the first marginal, as soon
as the second factor is a nonzero measure. -/
theorem ae_fst_of_ae_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {γ : Measure β} [SFinite ν] [SFinite γ] (hγ : γ ≠ 0)
    {P : α → Prop} (h : ∀ᵐ p ∂ν.prod γ, P p.1) : ∀ᵐ a ∂ν, P a := by
  have : (ae γ).NeBot := ae_neBot.2 hγ
  filter_upwards [Measure.ae_ae_of_ae_prod h] with a ha
  exact Filter.eventually_const.1 ha

/-- An almost-sure statement on a measurable full-measure subset, read through the subtype
measure, is an almost-sure statement on the whole space. -/
theorem ae_of_ae_comap_subtype {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {G : Set α} (hG : MeasurableSet G) (hae : ∀ᵐ a ∂ν, a ∈ G)
    {P : α → Prop} (h : ∀ᵐ x ∂(ν.comap (Subtype.val : G → α)), P x.val) :
    ∀ᵐ a ∂ν, P a := by
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact (ae_restrict_iff_subtype hG).2 h

/-- The subtype measure of a finite measure on a measurable set is finite. -/
theorem isFiniteMeasure_comap_subtype {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {G : Set α} (hG : MeasurableSet G) :
    IsFiniteMeasure (ν.comap (Subtype.val : G → α)) := by
  refine ⟨?_⟩
  rw [comap_subtype_coe_apply hG]
  exact measure_lt_top _ _

/-! ### From the marked maximal function to the consumer's ball bound, pointwise -/

/-- **One configuration.**  If the manuscript's maximal function `M(ρ_FE)` of a marked
configuration is finite, the environment of that configuration satisfies the consumers' ball
bound with `M = M(ρ_FE)(ω)`.  This is the pointwise content of
`ActualSpatialDensityBridge.ae_exists_ballBound_rootedFiniteEnergyDensity`; the density
identification `ofReal_rootFE_shift` needs only the re-rooting property of the action. -/
theorem exists_ballBound_of_ballMaximal_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (R : MarkedReRooting Ω) (hR : EnvReRooting R) {ω : Ω}
    (hω : ballMaximal R (rootFE R) ω < ∞) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode (R.env ω)) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M := by
  refine ⟨ballMaximal R (rootFE R) ω, hω.ne, fun r hr => ?_⟩
  have hdens : ∀ z : Plane, RootDensities.rootedFiniteEnergyDensity (decode (R.env ω)) z
      = ENNReal.ofReal (rootFE R (R.shift z ω)) := fun z => (ofReal_rootFE_shift hR ω z).symm
  simp_rw [hdens]
  exact setLIntegral_le_ballMaximal R (rootFE R) ω hr

/-! ### The reduction, for an arbitrary marked space over `ν` -/

/-- **`hMax` for `ν` from the third clause of `s:prop:maximal` on a marked space over `ν`.**

`hproj` says that almost-sure statements under the marked law transfer along the environment
observable to `ν`; for the product/subtype construction below it is proved
(`ae_fst_of_ae_prod`, `ae_of_ae_comap_subtype`).  `hmax` is the open input: the almost-sure
finiteness of the manuscript's maximal function `M(ρ_FE)` on the marked space. -/
theorem ae_exists_ballBound_of_marked (ν : Measure Env) {Ω : Type*} [MeasurableSpace Ω]
    (R : MarkedReRooting Ω) (μ : Measure Ω) (hR : EnvReRooting R)
    (hproj : ∀ P : Env → Prop, (∀ᵐ ω ∂μ, P (R.env ω)) → ∀ᵐ e ∂ν, P e)
    (hmax : ∀ᵐ ω ∂μ, ballMaximal R (rootFE R) ω < ∞) :
    ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M := by
  refine hproj (fun e => ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M) ?_
  filter_upwards [hmax] with ω hω
  exact exists_ballBound_of_ballMaximal_lt_top R hR hω

/-! ### The marked space over a good set of environments -/

section Good

variable (G : Set Env)

/-- The actual marked re-rooting of `Spatial/ActualMarkedBlockTransport`, restricted to a
re-rooting-stable set `G` of environments: the marked configuration is a pair of a good
environment and an independent uniform dyadic system, and re-rooting at `w` is the canonical
similarity action at unit scale on the environment together with the dyadic re-rooting of the
grid. -/
noncomputable def goodReRooting
    (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G) :
    MarkedReRooting (G × Grid) where
  env p := p.1.1
  grid p := p.2
  shift w p := (⟨translateEnv w p.1.1, hG w p.1.1 p.1.2⟩, translate w p.2)
  measurable_shift := by
    have h1 : Measurable fun q : (G × Grid) × Plane => translateEnv q.2 q.1.1.1 := by
      have hpair : Measurable fun q : (G × Grid) × Plane => ((q.1.1.1 : Env), q.2) :=
        ((measurable_subtype_coe.comp measurable_fst).comp measurable_fst).prodMk measurable_snd
      simpa only [Function.comp_def] using measurable_translateEnv.comp hpair
    have h2 : Measurable fun q : (G × Grid) × Plane => translate q.2 q.1.2 := by
      have hpair : Measurable fun q : (G × Grid) × Plane => (q.1.2, q.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      simpa only [Function.comp_def] using measurable_translate.comp hpair
    exact (h1.subtype_mk).prodMk h2
  shift_zero p := by
    apply Prod.ext
    · apply Subtype.ext
      show translateEnv 0 p.1.1 = p.1.1
      exact translateEnv_zero p.1.1
    · show translate 0 p.2 = p.2
      exact translate_zero p.2
  shift_shift w z p := by
    apply Prod.ext
    · apply Subtype.ext
      show translateEnv z (translateEnv w p.1.1) = translateEnv (w + z) p.1.1
      exact translateEnv_translateEnv w z p.1.1
    · show translate z (translate w p.2) = translate (w + z) p.2
      exact translate_translate w z p.2

variable {G}

@[simp] theorem goodReRooting_env (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G)
    (p : G × Grid) : (goodReRooting G hG).env p = p.1.1 := rfl

@[simp] theorem goodReRooting_grid
    (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G) (p : G × Grid) :
    (goodReRooting G hG).grid p = p.2 := rfl

@[simp] theorem goodReRooting_shift
    (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G) (w : Plane) (p : G × Grid) :
    (goodReRooting G hG).shift w p
      = (⟨translateEnv w p.1.1, hG w p.1.1 p.1.2⟩, translate w p.2) := rfl

/-- The re-rooting property holds on the good marked space: the environment component of
`shift z` is the canonical similarity action at unit scale. -/
theorem envReRooting_goodReRooting
    (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G) :
    EnvReRooting (goodReRooting G hG) :=
  fun p z => isSimilarity_translateEnv z p.1.1

/-- The good marked law: the subtype measure of `ν` on `G`, independently coupled with the
uniform dyadic law of `Forms/DyadicGridLaw`. -/
noncomputable def goodLaw (ν : Measure Env) : Measure (G × Grid) :=
  (ν.comap (Subtype.val : G → Env)).prod gridMeasure

/-- Almost-sure statements about the environment transfer from the good marked law to `ν`:
the marks are integrated out and the good set has full measure. -/
theorem ae_of_ae_goodLaw (ν : Measure Env) [IsFiniteMeasure ν] (hGm : MeasurableSet G)
    (hGae : ∀ᵐ e ∂ν, e ∈ G) {P : Env → Prop}
    (h : ∀ᵐ p ∂(goodLaw (G := G) ν), P p.1.1) : ∀ᵐ e ∂ν, P e := by
  have : IsFiniteMeasure (ν.comap (Subtype.val : G → Env)) :=
    isFiniteMeasure_comap_subtype ν hGm
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  refine ae_of_ae_comap_subtype hGm hGae ?_
  exact ae_fst_of_ae_prod (γ := gridMeasure) (IsProbabilityMeasure.ne_zero _) h

/-- **The consumers' `hMax`, from the third clause of `s:prop:maximal` on the good marked
space.**

`ν` is the environment law; `G` is any measurable full-measure set of environments stable
under re-rooting.  The only remaining input is `hmax`: the manuscript's maximal function
`M(ρ_FE)` of the rooted (FE) density is finite almost surely for the good marked law.  That
input is *not* proved here or in any import; it is the content of the dyadic block martingale
of `s:prop:maximal`, and this theorem does not certify it. -/
theorem ae_exists_ballBound_of_good_ballMaximal (ν : Measure Env) [IsFiniteMeasure ν]
    (hGm : MeasurableSet G) (hGae : ∀ᵐ e ∂ν, e ∈ G)
    (hG : ∀ (w : Plane) (e : Env), e ∈ G → translateEnv w e ∈ G)
    (hmax : ∀ᵐ p ∂(goodLaw (G := G) ν),
      ballMaximal (goodReRooting G hG) (rootFE (goodReRooting G hG)) p < ∞) :
    ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M :=
  ae_exists_ballBound_of_marked ν (goodReRooting G hG) (goodLaw ν)
    (envReRooting_goodReRooting hG)
    (fun _ h => ae_of_ae_goodLaw ν hGm hGae h) hmax

end Good

end ReflectedGMS.SpatialMaximalConsumerForm
