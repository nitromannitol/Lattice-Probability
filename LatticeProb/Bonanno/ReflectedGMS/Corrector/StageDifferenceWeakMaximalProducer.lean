/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageDifferenceWeakMaximalProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GatedResidualWeakMaximal
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageDifferenceWeakMaximal

/-!
# `s:eq:maximal` for the stage differences, from a two-grid marked space

`Corrector/StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal` — the input `hmax` of the
`hpatch`/`hconv` lane — had **no producer at all**: unlike `hsub`'s
`MarkedResidualWeakMaximal` and `hcopies`' `CopyDifferenceWeakMaximal`, no theorem anywhere
concluded it, not even conditionally on a marked space.  This module supplies the missing
consumer head, in the embedding-free shape of
`Corrector/GatedResidualWeakMaximal.markedResidualWeakMaximal_of_twoGridSpace`.

Everything it needs already exists:

* `Corrector/MarkedStageFieldCovariance.stageDifferenceField` is the **gated** stage difference
  `φ_a − φ_b` (`gatedApproximant` on both stages), and
  `rootedSpecificEnergyDensity_stageDifferenceField` is its similarity invariance, **unconditional
  and with no gate** — that is exactly `hcov` and `hinv`;
* `stageDifferenceField_eq_phi` identifies the gated field with `φ_a − φ_b` on the good event, so
  the gated density has the same maximal function and the same integral as the ungated one
  almost surely (`GoodEnvironmentSet`/`ae_mem_sublinearEvent`);
* measurability is `hmeas` alone, through
  `RootedSpecificEnergySpaceMeasurability.measurable_rootedSpecificEnergyDensity_prod`;
* the weak-`(1,1)` engine is `SpecificEnergyWeakMaximal.measure_exists_ball_gt_le`, with the
  project's absolute constant `512`.

The resulting `markedStageDifferenceWeakMaximal_of_twoGridSpace` takes the *same* marked-space
data as the residual head — `hchain`, `hdata`, `henv`, `hprojA`, `hmap`, `hshift`, `hdilate` —
so the two-grid space of `Spatial/AuxiliaryGridMarkedSpace` discharges it verbatim.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StageDifferenceWeakMaximalProducer

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicCoordinateAssembly HarmonicMainStatement
open MarkedBlockAveraging SpatialMaximalInequality SimilarityBlockAveraging
open SmallBlockResidualProducer SpecificEnergyWeakMaximal MarkedMassTransportProducer
open SpecificEnergyDensitySimilarity RootedSpecificEnergySpaceMeasurability
open MarkedStageFieldCovariance GatedResidualWeakMaximal StageDifferenceWeakMaximal
open LabelBijectionProducer

/-! ### The two stage-difference densities -/

/-- The stage-difference specific-energy density built from the raw block interpolants.  This is
the integrand of `SpecificEnergyConvergence.markedStageDefect` and the density whose maximal
function is `markedStageDifferenceMaximal`. -/
noncomputable def stageDifferenceDensityPhi (a b : ℕ) (p : MarkedEnvironment) (z : Plane) :
    ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode p.1)
    (fun v => phi (decode p.1) p.2 a v - phi (decode p.1) p.2 b v) z

/-- **The stage defect is the integral of that density at the origin.** -/
theorem markedStageDefect_eq (ν : Measure Env) (a b : ℕ) :
    SpecificEnergyConvergence.markedStageDefect ν a b
      = ∫⁻ p : MarkedEnvironment, stageDifferenceDensityPhi a b p 0 ∂ν.prod gridLaw := rfl

/-- The **gated** stage-difference density: the same expression on the gated field
`MarkedStageFieldCovariance.stageDifferenceField`, which is `0` off the good event.  Unlike
`stageDifferenceDensityPhi` this is measurable from `hmeas` alone and exactly similarity
covariant with no hypothesis. -/
noncomputable def gatedStageDifferenceDensity (a b : ℕ) (p : MarkedEnvironment) (z : Plane) :
    ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode p.1) (stageDifferenceField a b p) z

/-- On the good event the two densities agree. -/
theorem gatedStageDifferenceDensity_eq (a b : ℕ) {p : MarkedEnvironment}
    (hG : p.1 ∈ SublinearEvent) (z : Plane) :
    gatedStageDifferenceDensity a b p z = stageDifferenceDensityPhi a b p z := by
  show rootedSpecificEnergyDensity (decode p.1) (stageDifferenceField a b p) z = _
  rw [stageDifferenceField_eq_phi hG]
  rfl

/-! ### Measurability, from `hmeas` alone -/

theorem measurable_stageDifferenceLabel {α : Type*} [MeasurableSpace α] (a b : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → MarkedEnvironment) (hproj : Measurable proj) (n : ℕ) :
    Measurable fun ω : α => gatedApproximant a (proj ω) n - gatedApproximant b (proj ω) n := by
  have ha : Measurable fun ω : α => gatedApproximant a (proj ω) n := by
    have h : Measurable ((fun ω : MarkedEnvironment => gatedApproximant a ω n) ∘ proj) :=
      (hmeas a n).comp hproj
    simpa only [Function.comp_def] using h
  have hb : Measurable fun ω : α => gatedApproximant b (proj ω) n := by
    have h : Measurable ((fun ω : MarkedEnvironment => gatedApproximant b ω n) ∘ proj) :=
      (hmeas b n).comp hproj
    simpa only [Function.comp_def] using h
  exact ha.sub hb

/-- **Joint measurability of the gated stage-difference density, with no gate.**  The parameter
space's sigma-field is arbitrary, so this applies at the sub-sigma-field `𝒜.sigma`. -/
theorem measurable_gatedStageDifferenceDensity_prod {α : Type*} [MeasurableSpace α] (a b : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → MarkedEnvironment) (hproj : Measurable proj) :
    Measurable fun q : α × Plane => gatedStageDifferenceDensity a b (proj q.1) q.2 :=
  measurable_rootedSpecificEnergyDensity_prod (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      gatedApproximant a (proj ω) n - gatedApproximant b (proj ω) n)
    (measurable_stageDifferenceLabel a b hmeas proj hproj)

theorem measurable_gatedStageDifferenceDensity_zero {α : Type*} [MeasurableSpace α] (a b : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (proj : α → MarkedEnvironment) (hproj : Measurable proj) :
    Measurable fun ω : α => gatedStageDifferenceDensity a b (proj ω) 0 :=
  measurable_rootedSpecificEnergyDensity_zero (E := fun ω : α => (proj ω).1) hproj.fst
    (Ψ := fun (ω : α) (n : ℕ) =>
      gatedApproximant a (proj ω) n - gatedApproximant b (proj ω) n)
    (measurable_stageDifferenceLabel a b hmeas proj hproj)

/-! ### Exact similarity covariance, with no gate -/

/-- **The gated stage-difference density is exactly similarity covariant, with no hypothesis.**
This is `MarkedStageFieldCovariance.rootedSpecificEnergyDensity_stageDifferenceField` read at the
canonical relabelling. -/
theorem gatedStageDifferenceDensity_markedSimilarity (a b : ℕ) (s : ℝ) (u : Plane) (hs : 0 < s)
    (p : MarkedEnvironment) (z : Plane) :
    gatedStageDifferenceDensity a b (markedSimilarity s u hs p) (positiveSimilarity s u z)
      = gatedStageDifferenceDensity a b p z :=
  rootedSpecificEnergyDensity_stageDifferenceField a b
    (isSimilarityRelabel_similarityRelabel s u hs p.1) z

/-- `hcov`'s identity: the case `s = 1`, `u = z`. -/
theorem gatedStageDifferenceDensity_shift (a b : ℕ) (p : MarkedEnvironment) (z : Plane) :
    gatedStageDifferenceDensity a b (markedSimilarity 1 z one_pos p) 0
      = gatedStageDifferenceDensity a b p z := by
  have h := gatedStageDifferenceDensity_markedSimilarity a b 1 z one_pos p z
  rwa [show positiveSimilarity (1 : ℝ) z z = 0 by simp] at h

/-- `hinv`'s identity: the case `u = 0`, `z = 0`. -/
theorem gatedStageDifferenceDensity_dilate (a b : ℕ) (s : ℝ) (hs : 0 < s)
    (p : MarkedEnvironment) :
    gatedStageDifferenceDensity a b (markedSimilarity s 0 hs p) 0
      = gatedStageDifferenceDensity a b p 0 := by
  have h := gatedStageDifferenceDensity_markedSimilarity a b s 0 hs p 0
  rwa [show positiveSimilarity s (0 : Plane) 0 = 0 by simp] at h

/-! ### The gated density computes the maximal function and the defect almost surely -/

theorem ae_gate (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ p : MarkedEnvironment ∂ν.prod gridLaw, p.1 ∈ SublinearEvent :=
  ae_marked_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)

theorem lintegral_gatedStageDifferenceDensity (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (a b : ℕ) :
    (∫⁻ p : MarkedEnvironment, gatedStageDifferenceDensity a b p 0 ∂ν.prod gridLaw)
      = SpecificEnergyConvergence.markedStageDefect ν a b := by
  rw [markedStageDefect_eq]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_gate ν hν hFE] with p hG
  exact gatedStageDifferenceDensity_eq a b hG 0

theorem ae_densityMaximal_gated_eq (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (a b : ℕ) :
    ∀ᵐ p : MarkedEnvironment ∂ν.prod gridLaw,
      densityMaximal (gatedStageDifferenceDensity a b) p = markedStageDifferenceMaximal a b p := by
  filter_upwards [ae_gate ν hν hFE] with p hG
  exact densityMaximal_congr fun z => gatedStageDifferenceDensity_eq a b hG z

/-! ### The missing consumer head -/

/-- **`hpatch`/`hconv`'s maximal input, from a two-grid marked space.**

`StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal` had no producer of any kind.  This
is its consumer head, in the same embedding-free shape as
`GatedResidualWeakMaximal.markedResidualWeakMaximal_of_twoGridSpace`: no `MeasurableEmbedding`, no
pathwise gate, and no `hcov`/`hinv` — the last two are *theorems* here, because
`MarkedStageFieldCovariance` proves the similarity invariance of the gated stage-difference
density unconditionally.

What remains on the right of the arrow is the marked space and `hmeas`, the assembly's own
measurability of the gated interpolant.  The constant is the project's absolute `512`. -/
theorem markedStageDifferenceWeakMaximal_of_twoGridSpace
    {Ω : Type*} [MeasurableSpace Ω]
    {R : MarkedReRooting Ω} {S : ScaleAction R} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒜 : EnvSigma Ω} {F₀ : Ω → ℝ}
    (hchain : OriginChainRegular R) (hdata : SimilarityBlockData R S μ)
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
    have hmain := measure_exists_ball_gt_le hchain hdata henv
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

end ReflectedGMS.StageDifferenceWeakMaximalProducer
