/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GatedWeakMaximalOn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedResidualWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageDifferenceWeakMaximalProducer

/-!
# The weak-`L¹` maximal inequality on the manuscript's invariant domain

`Corrector/SpecificEnergyWeakMaximal` and `Corrector/GatedResidualWeakMaximal` prove the
manuscript's `s:eq:maximal` for an arbitrary marked density, and the three consumer heads that
turn it into `hsub`, `hpatch`/`hconv` and `hcopies`, from the **ungated** selected-block data
`SpatialMaximalInequality.OriginChainRegular` and
`SimilarityBlockAveraging.SimilarityBlockData`.

Under the singular-set manuscript's covering clause `μH[1] (uncoveredSet F) = 0` those two data
are **false as stated**: at an origin lying in no cell the origin dyadic chain selects no square,
and `Spatial/GoodMarkedScaleAction.blockScaleCovariantOn_goodScale` records why the failure is
genuine rather than merely unproved.  §3.1 of the manuscript says the same thing — blocks are
defined at points lying in a cell, *"hence Lebesgue-almost every point"*, and *"no claim is needed
about an uncovered singular point"*.  `Spatial/SimilarityBlockAveraging` therefore carries the
gated forms `OriginChainRegularOn`, `SimilarityBlockDataOn` and the
`InvariantDomain` conditions that let them be used, and proves the gated maximal inequality
`ballMaximal_lt_top_ae_similarityOn` / `measure_ballMaximal_gt_le_similarityOn`.

This module carries that single replacement up through the four statements the corrector lane
consumes.  Each theorem below is its ungated counterpart with

* `hchain : OriginChainRegular R` replaced by `hchain : OriginChainRegularOn R G`,
* `hdata : SimilarityBlockData R S μ` replaced by `hdata : SimilarityBlockDataOn R S μ G`,
* the extra hypothesis `hdom : InvariantDomain R S μ G`,

and **no other change of any kind**: the conclusions are literally the ungated ones, the constant
is the manuscript's `512`, and no hypothesis is added to or removed from the density `ρ`.  The
sole step of each proof that touches the block data is the application of
`SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity`, which becomes
`measure_ballMaximal_gt_le_similarityOn`.

**No regression.**  `SimilarityBlockAveraging.invariantDomain_univ`,
`blockEquivariant_of_blockEquivariantOn` and `similarityBlockData_of_similarityBlockDataOn` make
the full domain `G = Set.univ` an invariant domain on which the gated data is the ungated data, so
every ungated head remains derivable from its gated form and nothing that used to be provable has
been lost.

**This module proves no new mathematics.**  It is the domain-gating bookkeeping that the singular
covering clause forces on an already-checked chain of implications, and it certifies none of the
hypotheses of those implications.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS.GatedWeakMaximalOn

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open MarkedCentroidSublinearityProducer SmallBlockResidualProducer
open GridIndependenceCoupling GridIndependenceDifferenceBridge
open SpecificEnergyWeakMaximal MarkedMassTransportProducer SpecificEnergyDensitySimilarity
open LabelBijectionProducer RootedSpecificEnergySpaceMeasurability
open ResidualDensitySpaceMeasurability ResidualDensitySimilarity
open GatedResidualWeakMaximal MarkedStageFieldCovariance StageDifferenceWeakMaximal
open StageDifferenceWeakMaximalProducer

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### `s:eq:maximal` for a marked density, on the invariant domain -/

/-- **`s:eq:maximal` for an arbitrary marked density, on the manuscript's invariant domain.**

Verbatim `SpecificEnergyWeakMaximal.measure_densityMaximal_gt_le` with the ungated selected-block
data replaced by its gated form on an `InvariantDomain`.  Conclusion, constant and hypotheses on
`ρ` are unchanged; no finiteness of `ρ_ω(0)` is assumed. -/
theorem measure_densityMaximal_gt_le_on
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hchain : OriginChainRegularOn R G) (hdata : SimilarityBlockDataOn R S μ G)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ρ : Ω → Plane → ℝ≥0∞)
    (hcov : ∀ (ω : Ω) (z : Plane), ρ ω z = ρ (R.shift z ω) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω, ρ (S.dilate s ω) 0 = ρ ω 0)
    (hmeas0 : Measurable fun ω : Ω => ρ ω 0)
    (hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _ fun p => ρ p.1 p.2)
    {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
  classical
  -- measurability of the density in the space variable alone
  have hz : ∀ w : Ω, Measurable fun z : Plane => ρ w z := by
    intro w
    have hmk : @Measurable Plane (Ω × Plane) _
        (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) fun z : Plane => (w, z) :=
      Measurable.prodMk measurable_const measurable_id
    have h : Measurable ((fun p : Ω × Plane => ρ p.1 p.2) ∘ fun z : Plane => (w, z)) :=
      hjoint.comp hmk
    simpa only [Function.comp_def] using h
  -- the truncated inequality
  have key : ∀ N : ℕ,
      μ {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω}
        ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
    intro N
    have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
    have hmeasN : Measurable (truncatedRoot ρ N) :=
      (hmeas0.min measurable_const).ennreal_toReal
    have h0N : ∀ w : Ω, 0 ≤ truncatedRoot ρ N w := fun _ => ENNReal.toReal_nonneg
    have hlintN : (∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ) ≤ (N : ℝ≥0∞) := by
      calc (∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ)
          ≤ ∫⁻ _ : Ω, (N : ℝ≥0∞) ∂μ := lintegral_mono fun w => min_le_right _ _
        _ = (N : ℝ≥0∞) := by rw [lintegral_const, measure_univ, mul_one]
    have hintN : Integrable (truncatedRoot ρ N) μ :=
      integrable_toReal_of_lintegral_ne_top (hmeas0.min measurable_const).aemeasurable
        (ne_top_of_le_ne_top hNtop hlintN)
    have hinvN : S.InvariantFun (truncatedRoot ρ N) := by
      intro s hs w
      show (min (ρ (S.dilate s w) 0) (N : ℝ≥0∞)).toReal = (min (ρ w 0) (N : ℝ≥0∞)).toReal
      rw [hinv s hs w]
    have hdensN : @Measurable (Ω × Plane) ℝ
        (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
        fun p => truncatedRoot ρ N (R.shift p.2 p.1) := by
      have heq : (fun p : Ω × Plane => truncatedRoot ρ N (R.shift p.2 p.1))
          = fun p : Ω × Plane => (min (ρ p.1 p.2) (N : ℝ≥0∞)).toReal := by
        funext p
        show (min (ρ (R.shift p.2 p.1) 0) (N : ℝ≥0∞)).toReal
          = (min (ρ p.1 p.2) (N : ℝ≥0∞)).toReal
        rw [← hcov p.1 p.2]
      rw [heq]
      exact (hjoint.min measurable_const).ennreal_toReal
    have henvN : EnvironmentGrid R μ (truncatedRoot ρ N) 𝒜 :=
      { le := henv.le
        measurable_grid := henv.measurable_grid
        measurable_density := hdensN
        indep := henv.indep
        law := henv.law }
    have hbound := measure_ballMaximal_gt_le_similarityOn hdom hchain hdata henvN hmeasN h0N hintN
      hinvN ht
    -- the truncated ball maximal function is the maximal function of the truncated density
    have hballeq : ∀ w : Ω, ballMaximal R (truncatedRoot ρ N) w
        = densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w := by
      intro w
      show (⨆ r : ℝ, ⨆ _ : 0 < r, ballAverage R (truncatedRoot ρ N) r w)
          = ⨆ r : ℝ, ⨆ _ : 0 < r,
              densityBallAverage (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) r w
      refine iSup_congr fun r => iSup_congr fun _ => ?_
      show (ENNReal.ofReal (r ^ 2))⁻¹ *
          ∫⁻ z in Metric.closedBall (0 : Plane) r,
            ENNReal.ofReal (truncatedRoot ρ N (R.shift z w)) ∂volume
        = (ENNReal.ofReal (r ^ 2))⁻¹ *
          ∫⁻ z in Metric.closedBall (0 : Plane) r, min (ρ w z) (N : ℝ≥0∞) ∂volume
      congr 1
      refine lintegral_congr fun z => ?_
      show ENNReal.ofReal (min (ρ (R.shift z w) 0) (N : ℝ≥0∞)).toReal = min (ρ w z) (N : ℝ≥0∞)
      rw [← hcov w z]
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hNtop (min_le_right _ _))
    have hset : {w : Ω | ENNReal.ofReal t < ballMaximal R (truncatedRoot ρ N) w}
        = {w : Ω |
            ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w} := by
      ext w
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hballeq w]
    rw [hset] at hbound
    refine le_trans hbound ?_
    have hI : ENNReal.ofReal (∫ w, truncatedRoot ρ N w ∂μ)
        = ∫⁻ w : Ω, min (ρ w 0) (N : ℝ≥0∞) ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal hintN (Filter.Eventually.of_forall h0N)]
      refine lintegral_congr fun w => ?_
      show ENNReal.ofReal (min (ρ w 0) (N : ℝ≥0∞)).toReal = min (ρ w 0) (N : ℝ≥0∞)
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hNtop (min_le_right _ _))
    rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 512), hI,
      div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul' (mul_le_mul' le_rfl (lintegral_mono fun w => min_le_left _ _)) le_rfl
  -- the super-level sets of the truncated maximal functions increase to the untruncated one
  have hincl : {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ⊆ ⋃ N : ℕ, {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} := by
    intro w hw
    have hlt : ENNReal.ofReal t < densityMaximal ρ w := hw
    obtain ⟨r, hrpos, hlt2⟩ := (lt_densityMaximal_iff ρ ht w).1 hlt
    have hmonoFun : Monotone fun (N : ℕ) (z : Plane) => min (ρ w z) (N : ℝ≥0∞) := by
      intro N M hNM z
      exact min_le_min le_rfl (by exact_mod_cast hNM)
    have hsupint : (∫⁻ z in Metric.closedBall (0 : Plane) r, ρ w z ∂volume)
        = ⨆ N : ℕ, ∫⁻ z in Metric.closedBall (0 : Plane) r,
            min (ρ w z) (N : ℝ≥0∞) ∂volume := by
      rw [← lintegral_iSup (fun N => (hz w).min measurable_const) hmonoFun]
      exact lintegral_congr fun z => (iSup_min_natCast (ρ w z)).symm
    rw [hsupint, lt_iSup_iff] at hlt2
    obtain ⟨N, hN⟩ := hlt2
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    show ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w
    exact (lt_densityMaximal_iff (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) ht w).2
      ⟨r, hrpos, hN⟩
  have hmonoSet : Monotone fun N : ℕ => {ω : Ω |
      ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} := by
    intro N M hNM w hw
    have hw' : ENNReal.ofReal t
        < densityMaximal (fun w' z => min (ρ w' z) (N : ℝ≥0∞)) w := hw
    show ENNReal.ofReal t < densityMaximal (fun w' z => min (ρ w' z) (M : ℝ≥0∞)) w
    refine lt_of_lt_of_le hw' ?_
    exact densityMaximal_mono
      (fun w' z => min_le_min le_rfl (by exact_mod_cast hNM)) w
  calc μ {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω}
      ≤ μ (⋃ N : ℕ, {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω}) :=
        measure_mono hincl
    _ = ⨆ N : ℕ, μ {ω : Ω |
          ENNReal.ofReal t < densityMaximal (fun w z => min (ρ w z) (N : ℝ≥0∞)) ω} :=
        hmonoSet.measure_iUnion
    _ ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := iSup_le key

/-- **The same statement in the consumers' ball-integral shape**, on the invariant domain: the
shape of `GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal` and, after the trivial
conversion of the level from a real to an `ℝ≥0∞`, of
`SmallBlockResidualProducer.MarkedResidualWeakMaximal`. -/
theorem measure_exists_ball_gt_le_on
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hchain : OriginChainRegularOn R G) (hdata : SimilarityBlockDataOn R S μ G)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ρ : Ω → Plane → ℝ≥0∞)
    (hcov : ∀ (ω : Ω) (z : Plane), ρ ω z = ρ (R.shift z ω) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω, ρ (S.dilate s ω) 0 = ρ ω 0)
    (hmeas0 : Measurable fun ω : Ω => ρ ω 0)
    (hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _ fun p => ρ p.1 p.2)
    {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume}
      ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, ρ ω 0 ∂μ) / ENNReal.ofReal t := by
  have hset : {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, ρ ω z ∂volume}
      = {ω : Ω | ENNReal.ofReal t < densityMaximal ρ ω} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, lt_densityMaximal_iff ρ ht ω]
  rw [hset]
  exact measure_densityMaximal_gt_le_on hdom hchain hdata henv ρ hcov hinv hmeas0 hjoint ht

/-! ### The three consumer heads, on the invariant domain -/

/-- **`hsub`'s maximal input from a two-grid marked space, on the manuscript's invariant
domain.**

Verbatim `GatedResidualWeakMaximal.markedResidualWeakMaximal_of_twoGridSpace` with the gated
selected-block data.  Still an implication: it certifies none of its hypotheses. -/
theorem markedResidualWeakMaximal_of_twoGridSpaceOn
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hchain : OriginChainRegularOn R G) (hdata : SimilarityBlockDataOn R S μ G)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → MarkedEnvironment)
    (hprojA : @Measurable Ω MarkedEnvironment 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod gridLaw)
    (hshift : ∀ (z : Plane) (ω : Ω),
      proj (R.shift z ω) = markedSimilarity 1 z one_pos (proj ω))
    (hdilate : ∀ (t : ℝ) (ht : 0 < t) (ω : Ω),
      proj (S.dilate t ω) = markedSimilarity t 0 ht (proj ω)) :
    MarkedResidualWeakMaximal ν ms := by
  have hprojM : Measurable proj := hprojA.mono henv.le le_rfl
  have hgate : ∀ᵐ p : MarkedEnvironment ∂ν.prod gridLaw, p.1 ∈ SublinearEvent :=
    ae_marked_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  have hjointMarked : ∀ m : ℕ, Measurable fun q : MarkedEnvironment × Plane =>
      gatedResidualDensity ms m q.1 q.2 := fun m =>
    measurable_gatedResidualDensity_prod ms m hmeas id measurable_id
  have hzeroMarked : ∀ m : ℕ, Measurable fun p : MarkedEnvironment =>
      gatedResidualDensity ms m p 0 := fun m =>
    measurable_gatedResidualDensity_zero ms m hmeas id measurable_id
  have hcov : ∀ (m : ℕ) (ω : Ω) (z : Plane),
      gatedResidualDensity ms m (proj ω) z
        = gatedResidualDensity ms m (proj (R.shift z ω)) 0 := by
    intro m ω z
    rw [hshift z ω, gatedResidualDensity_shift]
  have hinv : ∀ (m : ℕ) (s : ℝ), 0 < s → ∀ ω : Ω,
      gatedResidualDensity ms m (proj (S.dilate s ω)) 0
        = gatedResidualDensity ms m (proj ω) 0 := by
    intro m s hs ω
    rw [hdilate s hs ω, gatedResidualDensity_dilate]
  have hmeas0 : ∀ m : ℕ, Measurable fun ω : Ω => gatedResidualDensity ms m (proj ω) 0 :=
    fun m => measurable_gatedResidualDensity_zero ms m hmeas proj hprojM
  have hjoint : ∀ m : ℕ, @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
      fun q => gatedResidualDensity ms m (proj q.1) q.2 :=
    fun m => @measurable_gatedResidualDensity_prod Ω 𝒜.sigma ms m hmeas proj hprojA
  refine ⟨ENNReal.ofReal 512, ENNReal.ofReal_ne_top, fun m lam hlam => ?_⟩
  rcases eq_or_ne lam ∞ with rfl | hlamtop
  · have hempty : {p : MarkedEnvironment | (∞ : ℝ≥0∞) < markedResidualMaximal ms m p}
        = (∅ : Set MarkedEnvironment) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_top
    rw [hempty, measure_empty]
    exact zero_le
  · have ht : 0 < lam.toReal := ENNReal.toReal_pos hlam.ne' hlamtop
    have hlt : ENNReal.ofReal lam.toReal = lam := ENNReal.ofReal_toReal hlamtop
    have hmain := measure_densityMaximal_gt_le_on hdom hchain hdata henv
      (fun ω z => gatedResidualDensity ms m (proj ω) z) (hcov m) (hinv m) (hmeas0 m)
      (hjoint m) ht
    rw [hlt] at hmain
    have hTmeas : MeasurableSet
        {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} :=
      measurableSet_lt measurable_const (measurable_densityMaximal (hjointMarked m))
    have hA : (ν.prod gridLaw)
          {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p}
        = μ {ω : Ω |
            lam < densityMaximal (fun ω' z => gatedResidualDensity ms m (proj ω') z) ω} := by
      rw [← hmap, Measure.map_apply hprojM hTmeas]
      rfl
    have hmono : (ν.prod gridLaw) {p : MarkedEnvironment | lam < markedResidualMaximal ms m p}
        ≤ (ν.prod gridLaw)
          {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} := by
      refine measure_mono_ae ?_
      filter_upwards [hgate] with p hp hmem
      have heq : densityMaximal (gatedResidualDensity ms m) p = markedResidualMaximal ms m p := by
        rw [markedResidualMaximal_eq]
        exact densityMaximal_congr fun z => gatedResidualDensity_eq ms m hp z
      show lam < densityMaximal (gatedResidualDensity ms m) p
      rw [heq]
      exact hmem
    have hL : (∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw)
        = ∫⁻ ω : Ω, gatedResidualDensity ms m (proj ω) 0 ∂μ := by
      have h1 : (∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw)
          = ∫⁻ p : MarkedEnvironment, gatedResidualDensity ms m p 0 ∂ν.prod gridLaw := by
        refine lintegral_congr_ae ?_
        filter_upwards [hgate] with p hp
        rw [gatedResidualDensity_eq ms m hp 0]
        exact SpecificEnergyWeakMaximal.rootedSpecificEnergyDensity_sub_comm (decode p.1)
          (fun v => phi (decode p.1) p.2 m v) (fun v => markedPotential ms p v) 0
      rw [h1, ← hmap, lintegral_map (hzeroMarked m) hprojM]
    calc (ν.prod gridLaw) {p : MarkedEnvironment | lam < markedResidualMaximal ms m p}
        ≤ (ν.prod gridLaw)
            {p : MarkedEnvironment | lam < densityMaximal (gatedResidualDensity ms m) p} := hmono
      _ = μ {ω : Ω |
            lam < densityMaximal (fun ω' z => gatedResidualDensity ms m (proj ω') z) ω} := hA
      _ ≤ ENNReal.ofReal 512 * (∫⁻ ω : Ω, gatedResidualDensity ms m (proj ω) 0 ∂μ) / lam :=
          hmain
      _ = ENNReal.ofReal 512 / lam *
            ∫⁻ p : MarkedEnvironment, markedSpecificGradientError ms m p ∂ν.prod gridLaw := by
          rw [hL, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

/-- **`hpatch`/`hconv`'s maximal input from a two-grid marked space, on the manuscript's
invariant domain.**

Verbatim `StageDifferenceWeakMaximalProducer.markedStageDifferenceWeakMaximal_of_twoGridSpace`
with the gated selected-block data. -/
theorem markedStageDifferenceWeakMaximal_of_twoGridSpaceOn
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hchain : OriginChainRegularOn R G) (hdata : SimilarityBlockDataOn R S μ G)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → MarkedEnvironment)
    (hprojA : @Measurable Ω MarkedEnvironment 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod gridLaw)
    (hshift : ∀ (z : Plane) (ω : Ω),
      proj (R.shift z ω) = markedSimilarity 1 z one_pos (proj ω))
    (hdilate : ∀ (t : ℝ) (ht : 0 < t) (ω : Ω),
      proj (S.dilate t ω) = markedSimilarity t 0 ht (proj ω)) :
    MarkedStageDifferenceWeakMaximal ν := by
  have hprojM : Measurable proj := hprojA.mono henv.le le_rfl
  refine ⟨ENNReal.ofReal 512, ENNReal.ofReal_ne_top, fun a b lam hlam => ?_⟩
  by_cases hlamtop : lam = ∞
  · have hempty : {p : MarkedEnvironment | lam < markedStageDifferenceMaximal a b p} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt, hlamtop]
      exact le_top
    rw [hempty, measure_empty]
    exact zero_le
  · set t : ℝ := lam.toReal with htdef
    have hlamt : ENNReal.ofReal t = lam := ENNReal.ofReal_toReal hlamtop
    have ht : 0 < t := ENNReal.toReal_pos hlam.ne' hlamtop
    -- the gated density, pulled back along `proj`
    have hjointMarked : Measurable fun q : MarkedEnvironment × Plane =>
        gatedStageDifferenceDensity a b q.1 q.2 :=
      measurable_gatedStageDifferenceDensity_prod a b hmeas id measurable_id
    have hzeroMarked : Measurable fun p : MarkedEnvironment =>
        gatedStageDifferenceDensity a b p 0 :=
      measurable_gatedStageDifferenceDensity_zero a b hmeas id measurable_id
    have hmeas0 : Measurable fun ω : Ω => gatedStageDifferenceDensity a b (proj ω) 0 :=
      measurable_gatedStageDifferenceDensity_zero a b hmeas proj hprojM
    have hjoint : @Measurable (Ω × Plane) ℝ≥0∞
        (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
        fun q => gatedStageDifferenceDensity a b (proj q.1) q.2 :=
      @measurable_gatedStageDifferenceDensity_prod Ω 𝒜.sigma a b hmeas proj hprojA
    have hcov : ∀ (ω : Ω) (z : Plane),
        gatedStageDifferenceDensity a b (proj ω) z
          = gatedStageDifferenceDensity a b (proj (R.shift z ω)) 0 := by
      intro ω z
      rw [hshift z ω, gatedStageDifferenceDensity_shift]
    have hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω,
        gatedStageDifferenceDensity a b (proj (S.dilate s ω)) 0
          = gatedStageDifferenceDensity a b (proj ω) 0 := by
      intro s hs ω
      rw [hdilate s hs ω, gatedStageDifferenceDensity_dilate]
    have hmain := measure_exists_ball_gt_le_on hdom hchain hdata henv
      (fun ω z => gatedStageDifferenceDensity a b (proj ω) z) hcov hinv hmeas0 hjoint ht
    -- transfer the level set to the marked space
    have hset : {p : MarkedEnvironment | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r,
              gatedStageDifferenceDensity a b p z ∂volume}
        = {p : MarkedEnvironment | ENNReal.ofReal t
            < densityMaximal (gatedStageDifferenceDensity a b) p} := by
      ext p
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
        lt_densityMaximal_iff (gatedStageDifferenceDensity a b) ht p]
    have hTmeas : MeasurableSet {p : MarkedEnvironment | ∃ r : ℝ, 0 < r ∧
        ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r,
              gatedStageDifferenceDensity a b p z ∂volume} := by
      rw [hset]
      exact measurableSet_lt measurable_const (measurable_densityMaximal hjointMarked)
    have hA : (ν.prod gridLaw)
          {p : MarkedEnvironment | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
            < ∫⁻ z in Metric.closedBall (0 : Plane) r,
                gatedStageDifferenceDensity a b p z ∂volume}
        = μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
            < ∫⁻ z in Metric.closedBall (0 : Plane) r,
                gatedStageDifferenceDensity a b (proj ω) z ∂volume} := by
      rw [← hmap, Measure.map_apply hprojM hTmeas]
      rfl
    have hL : (∫⁻ p : MarkedEnvironment, gatedStageDifferenceDensity a b p 0 ∂ν.prod gridLaw)
        = ∫⁻ ω : Ω, gatedStageDifferenceDensity a b (proj ω) 0 ∂μ := by
      rw [← hmap, lintegral_map hzeroMarked hprojM]
    -- the ungated level set is almost surely the gated one
    have hae : {p : MarkedEnvironment | lam < markedStageDifferenceMaximal a b p}
        =ᵐ[ν.prod gridLaw] {p : MarkedEnvironment | ENNReal.ofReal t
            < densityMaximal (gatedStageDifferenceDensity a b) p} := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [ae_densityMaximal_gated_eq ν hν hFE a b] with p hp
      rw [hp, hlamt]
    calc (ν.prod gridLaw) {p : MarkedEnvironment | lam < markedStageDifferenceMaximal a b p}
        = (ν.prod gridLaw) {p : MarkedEnvironment | ENNReal.ofReal t
            < densityMaximal (gatedStageDifferenceDensity a b) p} := measure_congr hae
      _ = μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
            < ∫⁻ z in Metric.closedBall (0 : Plane) r,
                gatedStageDifferenceDensity a b (proj ω) z ∂volume} := by rw [← hset, hA]
      _ ≤ ENNReal.ofReal 512
            * (∫⁻ ω : Ω, gatedStageDifferenceDensity a b (proj ω) 0 ∂μ)
            / ENNReal.ofReal t := hmain
      _ = ENNReal.ofReal 512 / lam * SpecificEnergyConvergence.markedStageDefect ν a b := by
          rw [← hL, lintegral_gatedStageDifferenceDensity ν hν hFE a b, hlamt,
            ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
          ring

/-- **`hcopies`' maximal input from a three-grid marked space, on the manuscript's invariant
domain.**

Verbatim `GatedResidualWeakMaximal.copyDifferenceWeakMaximal_of_twoGridSpace` with the gated
selected-block data.  Its two pathwise identities `hcov`, `hinv` are unchanged. -/
theorem copyDifferenceWeakMaximal_of_twoGridSpaceOn
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    {G : Set Ω} (hdom : InvariantDomain R S μ G)
    (hchain : OriginChainRegularOn R G) (hdata : SimilarityBlockDataOn R S μ G)
    (henv : EnvironmentGrid R μ F₀ 𝒜)
    (ν : Measure Env) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : Ω → CoupledSpace)
    (hprojA : @Measurable Ω CoupledSpace 𝒜.sigma _ proj)
    (hmap : μ.map proj = ν.prod (gridLaw.prod gridLaw))
    (hcov : ∀ (ω : Ω) (z : Plane),
      copyDifferenceDensity ms (proj ω) z = copyDifferenceDensity ms (proj (R.shift z ω)) 0)
    (hinv : ∀ s : ℝ, 0 < s → ∀ ω : Ω,
      copyDifferenceDensity ms (proj (S.dilate s ω)) 0 = copyDifferenceDensity ms (proj ω) 0) :
    CopyDifferenceWeakMaximal ν ms := by
  have hprojM : Measurable proj := hprojA.mono henv.le le_rfl
  have hjointCoupled : Measurable fun q : CoupledSpace × Plane =>
      copyDifferenceDensity ms q.1 q.2 :=
    measurable_copyDifferenceDensity_prod ms hmeas id measurable_id
  have hzeroCoupled : Measurable fun p : CoupledSpace => copyDifferenceDensity ms p 0 :=
    measurable_copyDifferenceDensity_zero ms hmeas id measurable_id
  have hmeas0 : Measurable fun ω : Ω => copyDifferenceDensity ms (proj ω) 0 :=
    measurable_copyDifferenceDensity_zero ms hmeas proj hprojM
  have hjoint : @Measurable (Ω × Plane) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω Plane 𝒜.sigma _) _
      fun q => copyDifferenceDensity ms (proj q.1) q.2 :=
    @measurable_copyDifferenceDensity_prod Ω 𝒜.sigma ms hmeas proj hprojA
  refine ⟨ENNReal.ofReal 512, ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  have hmain := measure_exists_ball_gt_le_on hdom hchain hdata henv
    (fun ω z => copyDifferenceDensity ms (proj ω) z) hcov hinv hmeas0 hjoint ht
  have hset : {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      = {p : CoupledSpace |
          ENNReal.ofReal t < densityMaximal (copyDifferenceDensity ms) p} := by
    ext p
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, lt_densityMaximal_iff (copyDifferenceDensity ms) ht p]
  have hTmeas : MeasurableSet {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume} := by
    rw [hset]
    exact measurableSet_lt measurable_const (measurable_densityMaximal hjointCoupled)
  have hA : (ν.prod (gridLaw.prod gridLaw))
        {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      = μ {ω : Ω | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r,
              copyDifferenceDensity ms (proj ω) z ∂volume} := by
    rw [← hmap, Measure.map_apply hprojM hTmeas]
    rfl
  have hL : (∫⁻ p : CoupledSpace, copyDifferenceDensity ms p 0 ∂ν.prod (gridLaw.prod gridLaw))
      = ∫⁻ ω : Ω, copyDifferenceDensity ms (proj ω) 0 ∂μ := by
    rw [← hmap, lintegral_map hzeroCoupled hprojM]
  show (ν.prod (gridLaw.prod gridLaw))
        {p : CoupledSpace | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r, copyDifferenceDensity ms p z ∂volume}
      ≤ ENNReal.ofReal 512 * (∫⁻ p : CoupledSpace, copyDifferenceDensity ms p 0
          ∂ν.prod (gridLaw.prod gridLaw)) / ENNReal.ofReal t
  rw [hA, hL]
  exact hmain

end ReflectedGMS.GatedWeakMaximalOn
