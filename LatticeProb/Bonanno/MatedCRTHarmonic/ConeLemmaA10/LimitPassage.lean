/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.LimitPassage at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LogShift
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVerPot
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirTime
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.GaussianTilt

/-!
# The test-pairing limit in DMS14 Lemma A.10

The finite Cameron--Martin shift in `GaussianTilt` is a covariance against a difference of
smooth circle mollifiers. This file identifies its two deterministic limits. First the
mollifier level tends to infinity at fixed circle radius. Then the radius tends to zero,
giving exactly the distribution `logRootingShift` constructed in `LogShift`.

The only Fubini estimate needed below is the existing uniform angular logarithm bound
`HeatDir.integral_abs_log_circle_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg LQGMetric.MarkovGermVer

/-- Averaging the smooth logarithmic potential of a test function over the unit circle is
pairing the test function with `-log (max ‖w‖ 1)`. -/
theorem circleAverage_logPot_zero_one (ψ : TestC) :
    Real.circleAverage (MarkovGermVer.logPot ψ) 0 1 =
      ∫ w : ℂ, ψ w * (-Real.log (max ‖w‖ (1 : ℝ))) := by
  let μθ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let F : ℂ × ℝ → ℝ := fun p => ψ p.1 * (-Real.log ‖circleMap 0 1 p.2 - p.1‖)
  have hFm : Measurable F := by
    exact (ψ.continuous.measurable.comp measurable_fst).mul
      ((Real.measurable_log.comp
        (((continuous_circleMap 0 1).measurable.comp measurable_snd).sub measurable_fst).norm).neg)
  have hFi : Integrable F (volume.prod μθ) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · refine ae_of_all _ fun w => ?_
      change IntegrableOn (fun x => F (w, x)) (Ioc 0 (2 * Real.pi)) volume
      simpa [μθ, F, mul_comm] using
        ((circleIntegrable_log_norm_sub_const (a := w) (c := 0) 1).neg.const_mul (ψ w)).1
    ·
      let B : ℂ → ℝ := fun w => |ψ w| *
        (2 * Real.pi * (2 * Real.posLog (‖w‖ + 1) - Real.log 1))
      have hBc : Continuous B := by
        dsimp [B]
        fun_prop
      have hBs : HasCompactSupport B := ψ.hasCompactSupport.abs.mul_right
      refine Integrable.mono' (hBc.integrable_of_hasCompactSupport hBs)
        hFm.aestronglyMeasurable.norm.integral_prod_right' (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [F, norm_mul, Real.norm_eq_abs, norm_neg]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      simpa [μθ, intervalIntegral.integral_of_le Real.two_pi_pos.le, B] using
        (LQGMetric.DGo.HeatDir.integral_abs_log_circle_le one_pos (0 : ℂ) w)
  have hswap := integral_integral_swap (f := fun w θ => F (w, θ)) hFi
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul, circleMap_zero_radius]
  change (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
      (∫ y, -Real.log ‖circleMap 0 1 θ - y‖ * ψ y) = _
  rw [show (fun θ => ∫ y, -Real.log ‖circleMap 0 1 θ - y‖ * ψ y) =
      fun θ => ∫ y, F (y, θ) by
        funext θ
        apply integral_congr_ae
        exact ae_of_all _ fun y => by simp [F, mul_comm]]
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change (2 * Real.pi)⁻¹ * ∫ θ, (∫ y, F (y, θ)) ∂μθ = _
  rw [← hswap]
  simp only [F, integral_const_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [F]
  dsimp [μθ]
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change (2 * Real.pi)⁻¹ * (ψ w *
      ∫ θ in (0 : ℝ)..2 * Real.pi, -Real.log ‖circleMap 0 1 θ - w‖) = _
  have hmean : (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap 0 1 θ - w‖ =
        Real.log (max ‖w‖ (1 : ℝ)) := by
    simpa [LQGMetric.CircleAvg.circLog, Real.circleAverage_def] using
      LQGMetric.CircleAvg.circLog_zero_one w
  rw [intervalIntegral.integral_neg]
  calc
    (2 * Real.pi)⁻¹ * (ψ w * -∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.log ‖circleMap 0 1 θ - w‖) =
        ψ w * (-((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.log ‖circleMap 0 1 θ - w‖)) := by ring
    _ = ψ w * (-Real.log (max ‖w‖ (1 : ℝ))) := by rw [hmean]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- At fixed positive circle radius, the covariance shift converges as the smooth mollifier is
removed. The limit is expressed using the smooth logarithmic potential of the test function. -/
theorem tendsto_finiteCircle_covShift (hh : IsNormalizedWPGFF h P) (γ : ℝ) (ψ : TestC0)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => γ * logCov ψ.1 (finiteCircleIndex n z ε).1) atTop
      (𝓝 (γ * (Real.circleAverage (MarkovGermVer.logPot ψ.1) z ε -
        Real.circleAverage (MarkovGermVer.logPot ψ.1) 0 1))) := by
  let f : C(ℂ, ℝ) := ⟨MarkovGermVer.logPot ψ.1, (contDiff_logPot ψ.1).continuous⟩
  have heq : ∀ n, logCov ψ.1 (finiteCircleIndex n z ε).1 =
      mollAvg (ofCont f) n z ε - mollAvg (ofCont f) n 0 1 := by
    intro n
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
  exact ((tendsto_mollAvg_ofCont f ε z).sub
    (tendsto_mollAvg_ofCont f 1 0)).const_mul γ

/-- After the fixed-radius mollifier limit, shrinking the rooting circle gives exactly the
distributional logarithmic shift of DMS14 Lemma A.10 on every mean-zero test function. -/
theorem tendsto_circle_covShift_logRootingShift (γ : ℝ) (z : ℂ) (ψ : TestC0) :
    Tendsto (fun ε : ℝ => γ * (Real.circleAverage (MarkovGermVer.logPot ψ.1) z ε -
      Real.circleAverage (MarkovGermVer.logPot ψ.1) 0 1)) (𝓝 0)
      (𝓝 (logRootingShift γ z ψ.1)) := by
  let φ : TestC := ψ.1
  have hcont : Continuous fun ε : ℝ =>
      Real.circleAverage (MarkovGermVer.logPot φ) z ε :=
    Real.Continuous.circleAverage (contDiff_logPot φ).continuous
  have ht : Tendsto (fun ε : ℝ =>
      Real.circleAverage (MarkovGermVer.logPot φ) z ε -
        Real.circleAverage (MarkovGermVer.logPot φ) 0 1) (𝓝 0)
      (𝓝 (Real.circleAverage (MarkovGermVer.logPot φ) z 0 -
        Real.circleAverage (MarkovGermVer.logPot φ) 0 1)) :=
    (hcont.tendsto 0).sub tendsto_const_nhds
  simp only [Real.circleAverage_zero] at ht
  have hA : Integrable fun w : ℂ => φ w * (-Real.log ‖w - z‖) :=
    (integrable_log_mul_test φ z).congr (ae_of_all _ fun w => by
      change -Real.log ‖z - w‖ * φ w = φ w * -Real.log ‖w - z‖
      rw [norm_sub_rev]
      ring)
  have hB : Integrable fun w : ℂ => φ w * (-Real.log (max ‖w‖ (1 : ℝ))) :=
    ((integrable_test_mul φ
      ⟨fun w => Real.log (max ‖w‖ (1 : ℝ)), continuous_log_max_norm_one⟩).neg).congr
        (ae_of_all _ fun w => by simp)
  have hpot : MarkovGermVer.logPot φ z =
      ∫ w, φ w * (-Real.log ‖w - z‖) := by
    unfold MarkovGermVer.logPot
    apply integral_congr_ae
    exact ae_of_all _ fun w => by
      change -Real.log ‖z - w‖ * φ w = φ w * -Real.log ‖w - z‖
      rw [norm_sub_rev]
      ring
  have htarget : logRootingShift γ z φ = γ *
      (MarkovGermVer.logPot φ z -
        Real.circleAverage (MarkovGermVer.logPot φ) 0 1) := by
    rw [logRootingShift_apply, circleAverage_logPot_zero_one, hpot]
    have heq : (fun w : ℂ => φ w * logRootingShiftFun γ z w) =
        fun w => γ * (φ w * (-Real.log ‖w - z‖) -
          φ w * (-Real.log (max ‖w‖ (1 : ℝ)))) := by
      funext w
      simp only [logRootingShiftFun]
      ring
    rw [heq, integral_const_mul, integral_sub hA hB]
  change Tendsto (fun ε : ℝ => γ *
      (Real.circleAverage (MarkovGermVer.logPot φ) z ε -
        Real.circleAverage (MarkovGermVer.logPot φ) 0 1)) (𝓝 0)
      (𝓝 (logRootingShift γ z φ))
  rw [htarget]
  convert ht.const_mul γ using 1 <;> ring

end MatedCRTHarmonic.ConeLemmaA10

