/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteMixtureLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteDensityMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgVar

/-!
# Finite-dimensional laws of the finite rooting mixture

At a fixed root, `map_finiteCircleTilt_eq_covShift` gives the Cameron--Martin law of
the complete process of mean-zero test pairings. This file first records the elementary
Tonelli adapter which mixes a jointly measurable family of densities over an independent
parameter. Applying it to the jointly measurable finite-circle Wick density gives the
finite-dimensional pairing law needed in the finite stage of DMS14 Lemma A.10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

/-- Tonelli adapter for mixing a jointly measurable family of density-weighted laws.

The parameter is the second coordinate of the product measure. The section hypothesis says
that every fixed-parameter weighted law has the indicated image law. -/
theorem map_prod_withDensity_of_section_maps
    {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {d : α × β → ℝ≥0∞} (hd : Measurable d) {f : α → δ} (hf : Measurable f)
    {g : α × β → δ} (hg : Measurable g)
    (hsec : ∀ y, (μ.withDensity fun x => d (x, y)).map f = μ.map fun x => g (x, y)) :
    ((μ.prod ν).withDensity d).map (fun p => f p.1) = (μ.prod ν).map g := by
  ext s hs
  have hfm : Measurable fun p : α × β => f p.1 := hf.comp measurable_fst
  have hleftSet : MeasurableSet ((fun p : α × β => f p.1) ⁻¹' s) :=
    hs.preimage hfm
  have hrightSet : MeasurableSet (g ⁻¹' s) := hs.preimage hg
  have hleftInt : Measurable (Set.indicator ((fun p : α × β => f p.1) ⁻¹' s) d) :=
    hd.indicator hleftSet
  have hrightInt : Measurable (Set.indicator (g ⁻¹' s) (1 : α × β → ℝ≥0∞)) :=
    measurable_one.indicator hrightSet
  calc
    ((μ.prod ν).withDensity d).map (fun p => f p.1) s =
        ∫⁻ p in (fun p : α × β => f p.1) ⁻¹' s, d p ∂μ.prod ν := by
      rw [Measure.map_apply hfm hs, withDensity_apply _ hleftSet]
    _ = ∫⁻ p, Set.indicator ((fun p : α × β => f p.1) ⁻¹' s) d p ∂μ.prod ν := by
      rw [lintegral_indicator hleftSet]
    _ = ∫⁻ y, ∫⁻ x, Set.indicator ((fun p : α × β => f p.1) ⁻¹' s) d (x, y) ∂μ ∂ν :=
      lintegral_prod_symm' _ hleftInt
    _ = ∫⁻ y, (μ.withDensity fun x => d (x, y)).map f s ∂ν := by
      apply lintegral_congr
      intro y
      change (∫⁻ x, (f ⁻¹' s).indicator (fun x => d (x, y)) x ∂μ) = _
      rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf),
        ← lintegral_indicator (hs.preimage hf)]
    _ = ∫⁻ y, (μ.map fun x => g (x, y)) s ∂ν := by
      apply lintegral_congr
      intro y
      exact congrArg (fun m : Measure δ => m s) (hsec y)
    _ = ∫⁻ y, ∫⁻ x, Set.indicator (g ⁻¹' s) (1 : α × β → ℝ≥0∞) (x, y) ∂μ ∂ν := by
      apply lintegral_congr
      intro y
      have hgy : Measurable fun x : α => g (x, y) := hg.comp measurable_prodMk_right
      change (μ.map (fun x => g (x, y))) s =
        ∫⁻ x, ((fun x => g (x, y)) ⁻¹' s).indicator (1 : α → ℝ≥0∞) x ∂μ
      rw [Measure.map_apply hgy hs]
      exact (lintegral_indicator_one (μ := μ) (hs.preimage hgy)).symm
    _ = ∫⁻ p, Set.indicator (g ⁻¹' s) (1 : α × β → ℝ≥0∞) p ∂μ.prod ν :=
      (lintegral_prod_symm' _ hrightInt).symm
    _ = (μ.prod ν).map g s := by
      rw [Measure.map_apply hg hs]
      exact lintegral_indicator_one (μ := μ.prod ν) hrightSet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The finite covariance shift against a fixed test is measurable in the root. -/
theorem measurable_finiteCircleCovShift (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ)
    (ε : ℝ) (ψ : TestC0) : Measurable fun z : ℂ =>
      γ * logCov ψ.1 (finiteCircleIndex n z ε).1 := by
  let f : C(ℂ, ℝ) :=
    ⟨MarkovGermVer.logPot ψ.1, (MarkovGermVer.contDiff_logPot ψ.1).continuous⟩
  have heq : ∀ z, logCov ψ.1 (finiteCircleIndex n z ε).1 =
      mollAvg (ofCont f) n z ε - mollAvg (ofCont f) n 0 1 := by
    intro z
    have hsym : logCov ψ.1 (finiteCircleIndex n z ε).1 =
        logCov (finiteCircleIndex n z ε).1 ψ.1 := by
      rw [← hh.1.covariance_eq ψ (finiteCircleIndex n z ε),
        ← hh.1.covariance_eq (finiteCircleIndex n z ε) ψ, covariance_comm]
    rw [hsym, logCov_eq_integral_logPot]
    change (∫ x, (circBump n z ε x - circBump n 0 1 x) * f x) = _
    simp_rw [sub_mul]
    rw [integral_sub (integrable_test_mul _ f) (integrable_test_mul _ f),
      integral_circBump_mul, integral_circBump_mul]
  simp_rw [heq]
  exact measurable_const.mul
    (((MatedCRTHarmonic.MoTPort.ConeArea3.measurable_mollAvg n ε).comp
      (measurable_const.prodMk measurable_id)).sub measurable_const)

/-- **Finite-stage mixture identity for DMS14 Lemma A.10.** Mix the fixed-root finite-circle
Wick tilt over an independent root with law `ν`. Every finite family `I` of mean-zero field
pairings then has the law of the corresponding base-field pairings translated, at root `z`, by
`γ * logCov ψ (finiteCircleIndex n z ε)`.

The only condition on the root measure is `SFinite ν`, exactly what Tonelli needs. -/
theorem map_finiteCircleTiltMixture_restrict_eq_covShift
    {ν : Measure ℂ} [SFinite ν] (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ)
    (ε : ℝ) (I : Finset TestC0) :
    ((P.prod ν).withDensity fun p : Ω × ℂ =>
        finiteCircleDensity (h := h) γ n p.2 ε p.1).map
          (fun p => I.restrict (pair0 (h p.1))) =
      (P.prod ν).map (fun p => I.restrict fun ψ =>
        pair0 (h p.1) ψ + γ * logCov ψ.1 (finiteCircleIndex n p.2 ε).1) := by
  letI := hh.1.gaussian.isProbabilityMeasure
  apply map_prod_withDensity_of_section_maps
      (measurable_finiteCircleDensity hh γ n ε)
      ((Finset.measurable_restrict I).comp (GFFLaw.measurable_pairProc hh.1.measurable))
  · refine measurable_pi_iff.2 fun ψ => ?_
    exact (((measurable_evalDist ψ.1.1).comp hh.1.measurable).comp measurable_fst).add
      ((measurable_finiteCircleCovShift hh γ n ε ψ.1).comp measurable_snd)
  · intro z
    have hpath := map_finiteCircleTilt_eq_covShift hh γ n z ε
    calc
      (P.withDensity (finiteCircleDensity (h := h) γ n z ε)).map
          (fun ω => I.restrict (pair0 (h ω))) =
          ((P.withDensity (finiteCircleDensity (h := h) γ n z ε)).map
            (fun ω => pair0 (h ω))).map I.restrict := by
        exact (Measure.map_map (Finset.measurable_restrict I)
          (GFFLaw.measurable_pairProc hh.1.measurable)).symm
      _ = (P.map fun ω ψ =>
          pair0 (h ω) ψ + γ * logCov ψ.1 (finiteCircleIndex n z ε).1).map
            I.restrict := by rw [hpath]
      _ = P.map (fun ω => I.restrict fun ψ =>
          pair0 (h ω) ψ + γ * logCov ψ.1 (finiteCircleIndex n z ε).1) := by
        exact Measure.map_map (Finset.measurable_restrict I)
          (measurable_pi_iff.2 fun ψ =>
            ((measurable_evalDist ψ.1).comp hh.1.measurable).add measurable_const)

end MatedCRTHarmonic.ConeLemmaA10

