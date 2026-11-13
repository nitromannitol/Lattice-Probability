/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteDensityLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.GaussianTilt
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-!
# The finite circle Wick density converges to its LQG approximation

At a fixed circle contained in the unit disk, the mollified Cameron--Martin density converges
almost surely to the exact circle-average Wick density. The variance correction is identified
using the existing circle-average covariance bridge and its exact logarithmic formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- On a circle contained in the unit disk, the regular covariance correction `betaAvg`
vanishes. -/
private lemma finiteDensity_betaAvg_eq_zero_of_inside_circle {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    LQGDimension.Osc37.betaAvg ε z = 0 := by
  unfold LQGDimension.Osc37.betaAvg
  apply Real.circleAverage_const_on_circle
  intro y hy
  rw [mem_sphere_iff_norm, abs_of_pos hε] at hy
  have hy1 : ‖y‖ ≤ 1 := by
    calc
      ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 := by rw [hy]; linarith
  rw [max_eq_right hy1, Real.log_one]

/-- The limiting variance of the finite mean-zero circle test is `-log ε` when its circle is
contained in the unit disk. -/
private lemma finiteCircleVariance_limit {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    LQGDimension.gffCircleCov ε z ε z = -Real.log ε := by
  rw [LQGDimension.Osc37.gffCircleCov_formula hε,
    LQGDimension.Osc37.aAvg_self hε,
    finiteDensity_betaAvg_eq_zero_of_inside_circle hε hz]
  ring

private lemma finiteCircleVariance_tendsto {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) :
    Tendsto (fun n => logCov (finiteCircleIndex n z ε).1
      (finiteCircleIndex n z ε).1) atTop (𝓝 (-Real.log ε)) := by
  have hcov := LQGMetric.CircleAvg.tendsto_logCov_circDiff
    hε one_pos hε one_pos z 0 z 0
  have hinc : incCov z ε 0 1 z ε 0 1 = -Real.log ε := by
    rw [← LQGMetric.CircleAvg.gffCircleCov_eq_incCov hε hε]
    exact finiteCircleVariance_limit hε hz
  rw [hinc] at hcov
  simpa [finiteCircleIndex] using hcov

/-- **Fixed-root finite-density limit.** If `H` is an a.e. version of the circle averages of a
normalized whole-plane GFF, then for every positive circle contained in the unit disk the finite
Wick densities converge almost surely to the exact circle-average density
`ε^(γ^2/2) exp(γ H_ε(z))`. -/
theorem ae_tendsto_finiteCircleDensity (hh : IsNormalizedWPGFF h P)
    (_hH : LQGDimension.IsGFFCircleAverage H P)
    (hagree : ∀ r, 0 < r → ∀ w,
      (fun ω => H r w ω) =ᵐ[P] fun ω => circleAvg (h ω) r w)
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (_hε1 : ε < 1) (z : ℂ)
    (hz : ‖z‖ + ε < 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n => finiteCircleDensity (h := h) γ n z ε ω) atTop
      (𝓝 (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z ω)))) := by
  have hmolZ : ∀ᵐ ω ∂P,
      Tendsto (fun n => mollAvg (h ω) n z ε) atTop (𝓝 (H ε z ω)) := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh.1 z hε, hagree ε hε z]
      with ω hlim hversion
    obtain ⟨a, ha⟩ := hlim
    have hae : circleAvg (h ω) ε z = a := CircleAvg.circleAvg_eq_of_tendsto ha
    have hlimit : a = H ε z ω := hae.symm.trans hversion.symm
    simpa only [hlimit] using ha
  have hmolBase : ∀ᵐ ω ∂P,
      Tendsto (fun n => mollAvg (h ω) n 0 1) atTop (𝓝 0) := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh.1 0 one_pos, hh.2]
      with ω hlim hnorm
    obtain ⟨a, ha⟩ := hlim
    have hae : circleAvg (h ω) 1 0 = a := CircleAvg.circleAvg_eq_of_tendsto ha
    have hlimit : a = 0 := hae.symm.trans hnorm
    simpa only [hlimit] using ha
  have hvar := finiteCircleVariance_tendsto hε (le_of_lt hz)
  filter_upwards [hmolZ, hmolBase] with ω hmolZω hmolBaseω
  have hdiff : Tendsto
      (fun n => mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) atTop
      (𝓝 (H ε z ω)) := by
    simpa only [sub_zero] using hmolZω.sub hmolBaseω
  have hcoeff : Tendsto
      (fun n => (γ ^ 2 / 2) * logCov (finiteCircleIndex n z ε).1
        (finiteCircleIndex n z ε).1) atTop
      (𝓝 ((γ ^ 2 / 2) * (-Real.log ε))) := hvar.const_mul (γ ^ 2 / 2)
  have hexponent : Tendsto
      (fun n => γ * (mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) -
        (γ ^ 2 / 2) * logCov (finiteCircleIndex n z ε).1
          (finiteCircleIndex n z ε).1) atTop
      (𝓝 (γ * H ε z ω - (γ ^ 2 / 2) * (-Real.log ε))) :=
    (hdiff.const_mul γ).sub hcoeff
  have hexp : Tendsto
      (fun n => Real.exp (γ * (mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) -
        (γ ^ 2 / 2) * logCov (finiteCircleIndex n z ε).1
          (finiteCircleIndex n z ε).1)) atTop
      (𝓝 (Real.exp (γ * H ε z ω - (γ ^ 2 / 2) * (-Real.log ε)))) :=
    (Real.continuous_exp.tendsto _).comp hexponent
  have htarget : Real.exp (γ * H ε z ω - (γ ^ 2 / 2) * (-Real.log ε)) =
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z ω) := by
    rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
    congr 1
    ring
  have hENN : Tendsto
      (ENNReal.ofReal ∘ fun n => Real.exp (γ *
        (mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) -
        (γ ^ 2 / 2) * logCov (finiteCircleIndex n z ε).1
          (finiteCircleIndex n z ε).1)) atTop
      (𝓝 (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H ε z ω)))) := by
    have h₀ := (ENNReal.continuous_ofReal.tendsto
      (Real.exp (γ * H ε z ω - (γ ^ 2 / 2) * (-Real.log ε)))).comp hexp
    simpa only [htarget] using h₀
  have hdef : ∀ n,
      finiteCircleDensity (h := h) γ n z ε ω = ENNReal.ofReal (Real.exp
        (γ * (mollAvg (h ω) n z ε - mollAvg (h ω) n 0 1) -
          (γ ^ 2 / 2) * logCov (finiteCircleIndex n z ε).1
            (finiteCircleIndex n z ε).1)) := by
    intro n
    simp only [finiteCircleDensity]
    congr 1
    congr 1
    ring
  exact hENN.congr' (Filter.Eventually.of_forall fun n => (hdef n).symm)

end MatedCRTHarmonic.ConeLemmaA10

