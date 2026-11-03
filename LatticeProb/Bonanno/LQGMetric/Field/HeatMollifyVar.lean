/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyVar at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A crude bound on the log-covariance of bounded compactly supported functions (P2-FHEAT)

`abs_logCov_le`: if `|φ| ≤ M`, `|ψ| ≤ N` and both vanish outside `B̄_R(0)`, then
`|logCov φ ψ| ≤ M N · πR² · (2R · πR² + C₁)` with `C₁ = ∫_{B̄_1(0)} |log|u|| du`.
This is the variance bound used for the truncation errors of `heatMollify` (FOUNDATIONS §3:
"variances via logCov"). Elementary: `|log t| ≤ t + 1_{t ≤ 1} |log t|` and the local
integrability of `log|·|` on `ℂ` (reused: `QuantumZipper.K3.locallyIntegrable_log_norm`,
QZ/Proofs/GFF/K3/GreenLower3.lean). Own elementary proof (no published source needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace LQGMetric

/-- `C₁ = ∫_{B̄_1(0)} |log|u|| du` -/
def logBallConst : ℝ := ∫ u in closedBall (0 : ℂ) 1, |Real.log ‖u‖|

/-- the integrand of `logBallConst` as a function on `ℂ` -/
def logBallFun (u : ℂ) : ℝ := (closedBall (0 : ℂ) 1).indicator (fun v => |Real.log ‖v‖|) u

lemma logBallFun_nonneg (u : ℂ) : 0 ≤ logBallFun u := by
  unfold logBallFun; exact indicator_nonneg (fun _ _ => abs_nonneg _) _

lemma integrable_logBallFun : Integrable logBallFun := by
  unfold logBallFun
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact (QuantumZipper.K3.locallyIntegrable_log_norm.integrableOn_isCompact
    (isCompact_closedBall 0 1)).abs

lemma integral_logBallFun : ∫ u, logBallFun u = logBallConst := by
  unfold logBallFun logBallConst
  exact integral_indicator measurableSet_closedBall

lemma logBallConst_nonneg : 0 ≤ logBallConst := by
  rw [← integral_logBallFun]; exact integral_nonneg logBallFun_nonneg

/-- `|log t| ≤ t + 1_{t ≤ 1} |log t|` for `t = ‖u‖`. -/
lemma abs_log_norm_le (u : ℂ) : |Real.log ‖u‖| ≤ ‖u‖ + logBallFun u := by
  unfold logBallFun
  by_cases hu : ‖u‖ ≤ 1
  · rw [indicator_of_mem (by simpa using hu)]
    linarith [norm_nonneg u]
  · push_neg at hu
    rw [indicator_of_notMem (by simpa using hu) , add_zero,
      abs_of_nonneg (Real.log_nonneg hu.le)]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

lemma volume_closedBall_toReal (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : ℂ) R)).toReal = Real.pi * R ^ 2 := by
  rw [Complex.volume_closedBall]
  simp [ENNReal.toReal_ofReal hR, mul_comm]

/-- **Crude log-covariance bound.** -/
theorem abs_logCov_le {φ ψ : ℂ → ℝ} {R M N : ℝ} (hR : 0 ≤ R) (hφ : ∀ x, |φ x| ≤ M)
    (hψ : ∀ y, |ψ y| ≤ N) (hφR : ∀ x, R < ‖x‖ → φ x = 0) (hψR : ∀ y, R < ‖y‖ → ψ y = 0) :
    |logCov φ ψ| ≤ M * N * (Real.pi * R ^ 2) * (2 * R * (Real.pi * R ^ 2) + logBallConst) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφ 0)
  have hN : 0 ≤ N := (abs_nonneg _).trans (hψ 0)
  set A := 2 * R * (Real.pi * R ^ 2) + logBallConst with hA
  set B : Set ℂ := closedBall (0 : ℂ) R
  have hBf : volume B < ⊤ := measure_closedBall_lt_top
  -- inner bound
  have hinner : ∀ x, ‖∫ y, φ x * (-Real.log ‖x - y‖) * ψ y‖ ≤
      B.indicator (fun _ => M * N * A) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      have hxR : ‖x‖ ≤ R := by simpa [B] using hx
      set F : ℂ → ℝ := fun y => M * N * (B.indicator (fun _ => 2 * R) y + logBallFun (x - y))
      have hFi : Integrable F := by
        refine Integrable.const_mul (Integrable.add ?_ (integrable_logBallFun.comp_sub_left x)) _
        exact (integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const hBf.ne)
      refine (norm_integral_le_of_norm_le hFi (Eventually.of_forall fun y => ?_)).trans ?_
      · by_cases hy : y ∈ B
        · have hyR : ‖y‖ ≤ R := by simpa [B] using hy
          simp only [F, indicator_of_mem hy, norm_mul, norm_neg, Real.norm_eq_abs]
          have h1 := abs_log_norm_le (x - y)
          have h2 : ‖x - y‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
          have h3 := logBallFun_nonneg (x - y)
          calc |φ x| * |Real.log ‖x - y‖| * |ψ y| = |φ x| * |ψ y| * |Real.log ‖x - y‖| := by
                ring
            _ ≤ M * N * (2 * R + logBallFun (x - y)) := by
                apply mul_le_mul (mul_le_mul (hφ x) (hψ y) (abs_nonneg _) hM) (by linarith)
                  (abs_nonneg _) (mul_nonneg hM hN)
        · have hy' : R < ‖y‖ := by simpa [B] using hy
          simp only [F, hψR y hy', mul_zero, norm_zero]
          exact mul_nonneg (mul_nonneg hM hN)
            (add_nonneg (indicator_nonneg (fun _ _ => by positivity) _) (logBallFun_nonneg _))
      · simp only [F]
        rw [integral_const_mul, integral_add ((integrable_indicator_iff measurableSet_closedBall).2
          (integrableOn_const hBf.ne)) (integrable_logBallFun.comp_sub_left x),
          integral_indicator measurableSet_closedBall, setIntegral_const,
          integral_sub_left_eq_self logBallFun volume x, integral_logBallFun]
        simp only [smul_eq_mul, measureReal_def, B, volume_closedBall_toReal R hR]
        rw [hA]; apply le_of_eq; ring
    · have hx' : R < ‖x‖ := by simpa [B] using hx
      simp [hφR x hx', indicator_of_notMem hx]
  have hA0 : 0 ≤ A := by rw [hA]; have := logBallConst_nonneg; positivity
  have hout := norm_integral_le_of_norm_le
    ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBf.ne))
    (Eventually.of_forall hinner)
  rw [integral_indicator measurableSet_closedBall, setIntegral_const] at hout
  simp only [smul_eq_mul, measureReal_def, B, volume_closedBall_toReal R hR] at hout
  unfold logCov
  rw [← Real.norm_eq_abs]
  refine hout.trans (le_of_eq ?_)
  ring

end LQGMetric
