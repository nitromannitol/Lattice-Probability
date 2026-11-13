/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteDensityScheffe at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteDensityProductAE
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteProcessMixture
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaExactMass
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.ScheffeAdapter

/-!
# Product-space Scheffé convergence of rooting densities

For a finite root measure supported strictly inside the normalization circle, the finite
Cameron--Martin densities converge in product-space `L¹` to the circle-average Wick density.
The exact masses follow from the finite process-mixture identity and the Gaussian circle-average
normalization, so no mass assumptions are added.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- Integrating a finite-circle rooting density over the field and a finite root measure gives
exactly the total root mass. -/
theorem lintegral_finiteCircleDensity_prod_eq_rootMass
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ) (ε : ℝ) :
    ∫⁻ p : Ω × ℂ, finiteCircleDensity (h := h) γ n p.2 ε p.1 ∂(P.prod ν) = ν Set.univ := by
  let d : Ω × ℂ → ℝ≥0∞ := fun p => finiteCircleDensity (h := h) γ n p.2 ε p.1
  let μ : Measure (Ω × ℂ) := (P.prod ν).withDensity d
  let X : Ω × ℂ → TestC0 → ℝ := fun p => pair0 (h p.1)
  let X' : Ω × ℂ → TestC0 → ℝ := fun p =>
    pair0 (h p.1) + finiteCircleCovShift γ n ε p.2
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hX : Measurable X := by
    exact (GFFLaw.measurable_pairProc hh.1.measurable).comp measurable_fst
  have hX' : Measurable X' := by
    refine measurable_pi_iff.2 fun ψ => ?_
    exact (((measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst).add
      ((measurable_finiteCircleCovShift hh γ n ε ψ).comp measurable_snd)
  have hmap := map_finiteCircleTiltMixture_eq_covShift (ν := ν) hh γ n ε
  have hmass : μ Set.univ = (P.prod ν) Set.univ := by
    calc
      μ Set.univ = (μ.map X) Set.univ := by
        rw [Measure.map_apply hX MeasurableSet.univ]
        rfl
      _ = ((P.prod ν).map X') Set.univ := by
        exact congrArg (fun m : Measure (TestC0 → ℝ) => m Set.univ) (by
          simpa only [μ, d, X, X'] using hmap)
      _ = (P.prod ν) Set.univ := by
        rw [Measure.map_apply hX' MeasurableSet.univ]
        rfl
  have hwith : μ Set.univ = ∫⁻ p, d p ∂(P.prod ν) := by
    change ((P.prod ν).withDensity d) Set.univ = _
    rw [withDensity_apply d MeasurableSet.univ, Measure.restrict_univ]
  have hprod : (P.prod ν) Set.univ = ν Set.univ := by
    rw [Measure.prod_apply MeasurableSet.univ]
    simp
  calc
    _ = μ Set.univ := hwith.symm
    _ = (P.prod ν) Set.univ := hmass
    _ = ν Set.univ := hprod

/-- The limiting circle-average Wick density has the same total mass over the product law. -/
theorem lintegral_circleAvgDensity_prod_eq_rootMass
    (hh : IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ w,
      (fun ω => H r w ω) =ᵐ[P] fun ω => circleAvg (h ω) r w)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ + ε < 1) :
    ∫⁻ p : Ω × ℂ, ENNReal.ofReal
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h p.1) ε p.2)) ∂(P.prod ν) = ν Set.univ := by
  let d : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h p.1) ε p.2))
  letI : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hd : Measurable d := by
    dsimp [d]
    have hp : Measurable fun p : Ω × ℂ =>
        ((h p.1, ε, p.2) : DistC × ℝ × ℂ) :=
      (hh.1.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)
    have hc : Measurable fun p : Ω × ℂ => circleAvg (h p.1) ε p.2 :=
      LQGMetric.measurable_circleAvg.comp
        (f := fun p : Ω × ℂ => ((h p.1, ε, p.2) : DistC × ℝ × ℂ)) hp
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hc)))
  have hmass : ∀ᵐ z ∂ν, ∫⁻ ω, d (ω, z) ∂P = 1 := by
    filter_upwards [hν] with z hz
    have hzn : ‖z‖ + ε ≤ 1 := le_of_lt hz
    have hEq : (fun ω => d (ω, z)) =ᵐ[P] fun ω => ENNReal.ofReal
        (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z ω)) := by
      filter_upwards [hagree ε hε z] with ω heq
      simp only [d, heq]
    rw [lintegral_congr_ae hEq]
    exact lintegral_dens_eq_one hH γ hε hzn
  calc
    _ = ∫⁻ z, ∫⁻ ω, d (ω, z) ∂P ∂ν := lintegral_prod_symm' d hd
    _ = ∫⁻ z, 1 ∂ν := lintegral_congr_ae hmass
    _ = ν Set.univ := by simp

/-- Product-space `L¹` convergence of finite rooting densities to the circle-average Wick
density. The root measure only needs to be finite and almost surely supported at distance more
than `ε` from the normalization boundary. -/
theorem tendsto_integral_abs_sub_finiteCircleDensity_prod
    (hh : IsNormalizedWPGFF h P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ w,
      (fun ω => H r w ω) =ᵐ[P] fun ω => circleAvg (h ω) r w)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ + ε < 1) :
    Tendsto
      (fun n => ∫ p : Ω × ℂ, |(finiteCircleDensity (h := h) γ n p.2 ε p.1).toReal -
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h p.1) ε p.2)| ∂(P.prod ν))
      atTop (𝓝 0) := by
  let μ : Measure (Ω × ℂ) := P.prod ν
  let d : ℕ → Ω × ℂ → ℝ≥0∞ := fun n p =>
    finiteCircleDensity (h := h) γ n p.2 ε p.1
  let f : ℕ → Ω × ℂ → ℝ := fun n p => (d n p).toReal
  let g : Ω × ℂ → ℝ := fun p =>
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg (h p.1) ε p.2)
  let dg : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (g p)
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hd : ∀ n, Measurable (d n) := by
    intro n
    exact measurable_finiteCircleDensity hh γ n ε
  have hg : Measurable g := by
    dsimp [g]
    have hp : Measurable fun p : Ω × ℂ =>
        ((h p.1, ε, p.2) : DistC × ℝ × ℂ) :=
      (hh.1.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd)
    have hc : Measurable fun p : Ω × ℂ => circleAvg (h p.1) ε p.2 :=
      LQGMetric.measurable_circleAvg.comp
        (f := fun p : Ω × ℂ => ((h p.1, ε, p.2) : DistC × ℝ × ℂ)) hp
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hc))
  have hgn : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    positivity
  have hdg : Measurable dg := ENNReal.measurable_ofReal.comp hg
  have hdg_mass : ∫⁻ p, dg p ∂μ = ν Set.univ := by
    simpa only [μ, dg, g] using
      lintegral_circleAvgDensity_prod_eq_rootMass (h := h) hh hH hagree γ hε hν
  have hmass : ∀ n, ∫⁻ p, d n p ∂μ = ν Set.univ := by
    intro n
    simpa only [μ, d] using lintegral_finiteCircleDensity_prod_eq_rootMass
      (ν := ν) hh γ n ε
  have hfinite : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
  have hgint : Integrable g μ := by
    have hto : Integrable (fun p => (dg p).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top (μ := μ) hdg.aemeasurable
        (by rw [hdg_mass]; exact hfinite)
    apply hto.congr
    filter_upwards with p
    dsimp [dg]
    rw [ENNReal.toReal_ofReal (hgn p)]
  have hgintegral : ∫ p, g p ∂μ = (ν Set.univ).toReal := by
    have hto := integral_toReal (μ := μ) hdg.aemeasurable
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)
    have hto' : ∫ p, (dg p).toReal ∂μ = (ν Set.univ).toReal := by
      rw [hto, hdg_mass]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun p => by
      dsimp [dg]
      rw [ENNReal.toReal_ofReal (hgn p)])).trans hto'
  have hfi : ∀ n, Integrable (f n) μ := by
    intro n
    have hto : Integrable (fun p => (d n p).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top (μ := μ) (hd n).aemeasurable
        (by rw [hmass n]; exact hfinite)
    exact hto
  have hfintegral : ∀ n, ∫ p, f n p ∂μ = (ν Set.univ).toReal := by
    intro n
    have hto := integral_toReal (μ := μ) (hd n).aemeasurable
      (Filter.Eventually.of_forall fun p => by
        dsimp [d, finiteCircleDensity]
        exact ENNReal.ofReal_lt_top)
    simpa only [f, d, μ] using hto.trans (by rw [hmass n])
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    exact ENNReal.measurable_toReal.comp (hd n)
  have hfnn : ∀ n, ∀ᵐ p ∂μ, 0 ≤ f n p := by
    intro n
    exact Filter.Eventually.of_forall fun p => ENNReal.toReal_nonneg
  have hgn_ae : ∀ᵐ p ∂μ, 0 ≤ g p := Filter.Eventually.of_forall hgn
  have haeENN := ae_tendsto_finiteCircleDensity_prod hh hH hagree γ hε hν
  have hae : ∀ᵐ p ∂μ, Tendsto (fun n => f n p) atTop (𝓝 (g p)) := by
    filter_upwards [haeENN] with p hp
    have hp' := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hp
    convert hp' using 1 <;> simp [Function.comp_def, f, d, g,
      ENNReal.toReal_ofReal (hgn p)]
  have hint : Tendsto (fun n => ∫ p, f n p ∂μ) atTop (𝓝 (∫ p, g p ∂μ)) := by
    rw [show (fun n => ∫ p, f n p ∂μ) = fun _ : ℕ => (ν Set.univ).toReal by
      funext n
      exact hfintegral n]
    rw [hgintegral]
    exact tendsto_const_nhds
  simpa only [μ, f, d, g] using tendsto_integral_abs_sub_zero_of_scheffe
    hfm hg hfi (by simpa only [μ] using hgint) hfnn hgn_ae hae hint

end MatedCRTHarmonic.ConeLemmaA10

