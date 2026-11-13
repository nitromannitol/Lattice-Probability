/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CylinderLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteProcessMixture
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingTiltLimit

/-!
# Finite-coordinate limit of the rooted pairing process

The scalar covariance limit from `RootingTiltLimit` lifts coordinatewise to every finite
cylinder of the mean-zero pairing process. This is only a deterministic, pointwise limit of
the translated vectors; it does not assert convergence of their laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The finite vector of translated field pairings has the canonical logarithmic rooting shift
as its iterated limit: first `n → ∞` at fixed positive radius, then `ε → 0+`.

This is the finite-product lift of
`finiteCircle_covShift_iterated_limit_normalized`; the unit-disk hypothesis removes the final
unit-circle normalization from the endpoint. -/
theorem finiteCircleCovShift_restrict_iterated_limit
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) (I : Finset TestC0) (ω : Ω)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n => I.restrict (pair0 (h ω) + finiteCircleCovShift γ n ε z)) atTop
        (𝓝 (I.restrict fun ψ => pair0 (h ω) ψ + γ *
          (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) z ε -
            Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)))) ∧
    Tendsto
      (fun ε : ℝ => I.restrict fun ψ => pair0 (h ω) ψ + γ *
        (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) z ε -
          Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1))
      (𝓝[Ioi (0 : ℝ)] 0)
      (𝓝 (I.restrict (pair0 (h ω + logRootingShift γ z)))) := by
  constructor
  · intro ε hε
    rw [tendsto_pi_nhds]
    intro ψ
    have hψ :=
      (finiteCircle_covShift_iterated_limit_normalized hh γ hz (ψ : TestC0)).1 ε hε
    simpa only [Finset.restrict, finiteCircleCovShift, Pi.add_apply] using
      hψ.const_add (pair0 (h ω) (ψ : TestC0))
  · rw [tendsto_pi_nhds]
    intro ψ
    have hψ :=
      (finiteCircle_covShift_iterated_limit_normalized hh γ hz (ψ : TestC0)).2
    rw [normalize_logRootingShift_eq_self hz] at hψ
    simpa only [Finset.restrict, pair0, Pi.add_apply, add_apply] using
      hψ.const_add (pair0 (h ω) (ψ : TestC0))

/-- If the root law is supported almost everywhere in the open unit disk, the finite-coordinate
iterated limit holds almost everywhere under the independent field-root product law. -/
theorem ae_finiteCircleCovShift_restrict_iterated_limit_prod
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) (I : Finset TestC0)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ p ∂(P.prod ν),
      (∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun n => I.restrict
            (pair0 (h p.1) + finiteCircleCovShift γ n ε p.2)) atTop
          (𝓝 (I.restrict fun ψ => pair0 (h p.1) ψ + γ *
            (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
              Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)))) ∧
      Tendsto
        (fun ε : ℝ => I.restrict fun ψ => pair0 (h p.1) ψ + γ *
          (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) p.2 ε -
            Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1))
        (𝓝[Ioi (0 : ℝ)] 0)
        (𝓝 (I.restrict (pair0 (h p.1 + logRootingShift γ p.2)))) := by
  have hroot : ∀ᵐ p ∂(P.prod ν), p.2 ∈ ball (0 : ℂ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae hν
  filter_upwards [hroot] with p hp
  exact finiteCircleCovShift_restrict_iterated_limit hh γ I p.1 hp

end MatedCRTHarmonic.ConeLemmaA10

