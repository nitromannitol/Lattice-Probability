/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingTiltLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.DistNormalization
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LimitPassage

/-!
# The iterated finite-rooting limit on test pairings

This file joins the two deterministic covariance limits following the exact finite
Cameron--Martin identity in `map_finiteCircleTilt_eq_covShift`. The conclusion is deliberately
about one mean-zero test pairing: convergence of these deterministic shifts alone does not assert
convergence, or equality, of the full field laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **The finite rooting covariance has the normalized logarithmic shift as its iterated
limit.** For every fixed positive circle radius, first remove the smooth mollifier
(`n → ∞`). Then shrink the circle through positive radii. For a root in the open unit disk,
the endpoint is the canonical unit-circle-normalized version of the DMS14 logarithmic shift.

This is an iterated scalar limit for the test pairing `ψ`; it does not promote convergence of
test means to convergence of field laws. -/
theorem finiteCircle_covShift_iterated_limit_normalized (hh : IsNormalizedWPGFF h P)
    (γ : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (ψ : TestC0) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => γ * logCov ψ.1 (finiteCircleIndex n z ε).1) atTop
        (𝓝 (γ * (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) z ε -
          Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1)))) ∧
    Tendsto (fun ε : ℝ => γ *
        (Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) z ε -
          Real.circleAverage (LQGMetric.MarkovGermVer.logPot ψ.1) 0 1))
      (𝓝[Ioi (0 : ℝ)] 0)
      (𝓝 ((addConst (logRootingShift γ z)
        (-circleAvg (logRootingShift γ z) 1 0)) ψ.1)) := by
  constructor
  · intro ε hε
    exact tendsto_finiteCircle_covShift hh γ ψ z hε
  · rw [normalize_logRootingShift_eq_self hz]
    exact (tendsto_circle_covShift_logRootingShift γ z ψ).mono_left
      nhdsWithin_le_nhds

end MatedCRTHarmonic.ConeLemmaA10

