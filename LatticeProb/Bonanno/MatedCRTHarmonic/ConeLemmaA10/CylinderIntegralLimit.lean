/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CylinderIntegralLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CylinderLimit

/-!
# Bounded continuous observables of the rooted finite cylinders

The almost-everywhere finite-coordinate limits from `CylinderLimit` pass through bounded
continuous cylinder observables and then through the product integral by dominated convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- A bounded continuous observable of a finite rooted field cylinder passes through both
iterated finite-circle covariance limits after integration against the independent field-root
product law. The hypotheses on the root law are exactly those needed by
`ae_finiteCircleCovShift_restrict_iterated_limit_prod`.

This is an integral convergence statement; it does not assert equality or convergence of the
tilted process laws. -/
theorem tendsto_integral_cylinder_observable_iterated_limit
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) (I : Finset TestC0)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1)
    (F : (I → ℝ) → ℝ) (hF : Continuous F)
    (hF_bounded : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n => ∫ p : Ω × ℂ,
          F (I.restrict (pair0 (h p.1) + finiteCircleCovShift γ n ε p.2)) ∂(P.prod ν))
        atTop
        (𝓝 (∫ p : Ω × ℂ,
          F (I.restrict fun ψ => pair0 (h p.1) ψ + γ *
            (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
              Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)) ∂(P.prod ν)))) ∧
    Tendsto
      (fun ε : ℝ => ∫ p : Ω × ℂ,
        F (I.restrict fun ψ => pair0 (h p.1) ψ + γ *
          (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
            Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)) ∂(P.prod ν))
      (𝓝[Ioi (0 : ℝ)] 0)
      (𝓝 (∫ p : Ω × ℂ,
        F (I.restrict (pair0 (h p.1 + logRootingShift γ p.2))) ∂(P.prod ν))) := by
  rcases hF_bounded with ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB_nonneg : 0 ≤ B := le_max_right C 0
  have hF_bound : ∀ x, ‖F x‖ ≤ B := fun x => (hC x).trans (le_max_left C 0)
  let μ : Measure (Ω × ℂ) := P.prod ν
  let X : ℕ → ℝ → Ω × ℂ → I → ℝ := fun n ε p =>
    I.restrict (pair0 (h p.1) + finiteCircleCovShift γ n ε p.2)
  let Y : ℝ → Ω × ℂ → I → ℝ := fun ε p =>
    I.restrict fun ψ => pair0 (h p.1) ψ + γ *
      (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
        Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)
  let Z : Ω × ℂ → I → ℝ := fun p =>
    I.restrict (pair0 (h p.1 + logRootingShift γ p.2))
  haveI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hB_integrable : Integrable (fun _ : Ω × ℂ => B) μ := integrable_const B
  have hlimits := ae_finiteCircleCovShift_restrict_iterated_limit_prod
    (ν := ν) hh γ I hν
  have hlimits_first (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ p ∂μ, Tendsto (fun n => X n ε p) atTop (𝓝 (Y ε p)) := by
    filter_upwards [hlimits] with p hp
    exact hp.1 ε hε
  have hlimits_second :
      ∀ᵐ p ∂μ, Tendsto (fun ε : ℝ => Y ε p) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (Z p)) := by
    filter_upwards [hlimits] with p hp
    exact hp.2
  have hX_meas (n : ℕ) (ε : ℝ) : Measurable (X n ε) := by
    dsimp [X]
    apply (Finset.measurable_restrict I).comp
    refine measurable_pi_iff.2 fun ψ => ?_
    exact (((measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst).add
      ((measurable_finiteCircleCovShift hh γ n ε ψ).comp measurable_snd)
  have hF_X_meas (n : ℕ) (ε : ℝ) : AEStronglyMeasurable (fun p => F (X n ε p)) μ := by
    exact (hF.measurable.comp (hX_meas n ε)).aestronglyMeasurable
  have hB_dom (n : ℕ) (ε : ℝ) : ∀ᵐ p ∂μ, ‖F (X n ε p)‖ ≤ B :=
    Filter.Eventually.of_forall fun p => hF_bound (X n ε p)
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hpointwise : ∀ᵐ p ∂μ,
        Tendsto (fun n => F (X n ε p)) atTop (𝓝 (F (Y ε p))) := by
      filter_upwards [hlimits_first ε hε] with p hp
      exact hF.continuousAt.tendsto.comp hp
    have hconv := tendsto_integral_of_dominated_convergence
      (bound := fun _ : Ω × ℂ => B)
      (fun n => hF_X_meas n ε)
      hB_integrable
      (fun n => hB_dom n ε)
      hpointwise
    simpa only [μ, X, Y] using hconv
  · have hY_meas (ε : ℝ) (hε : 0 < ε) :
        AEStronglyMeasurable (fun p => F (Y ε p)) μ := by
      apply aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => hF_X_meas n ε)
      filter_upwards [hlimits_first ε hε] with p hp
      exact hF.continuousAt.tendsto.comp hp
    have hY_meas_eventually :
        ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
          AEStronglyMeasurable (fun p => F (Y ε p)) μ := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hY_meas ε (by simpa using hε)
    have hY_bound_eventually :
        ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
          ∀ᵐ p ∂μ, ‖F (Y ε p)‖ ≤ B :=
      Filter.Eventually.of_forall fun ε =>
        Filter.Eventually.of_forall fun p => hF_bound (Y ε p)
    have hpointwise : ∀ᵐ p ∂μ,
        Tendsto (fun ε : ℝ => F (Y ε p)) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (F (Z p))) := by
      filter_upwards [hlimits_second] with p hp
      exact hF.continuousAt.tendsto.comp hp
    have hconv := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (bound := fun _ : Ω × ℂ => B)
      hY_meas_eventually hY_bound_eventually hB_integrable hpointwise
    simpa only [μ, Y, Z] using hconv

end MatedCRTHarmonic.ConeLemmaA10

