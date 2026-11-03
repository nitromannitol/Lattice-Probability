/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer2S at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2A

/-!
# A Schur bound for the logarithmic covariance (task P2-MKD2)

`logCov_self_le_schur`: for `p` continuous, vanishing outside `B̄_R(0)`,
`logCov p p ≤ 2 L_R ∫ p²` with `L_R = 2R · π(2R)² + ∫_{B̄₁} |log|u|| du`.

Schur test for the kernel `|log|x−y||` restricted to `B̄_R × B̄_R` (dominated by the integrable
translation kernel `g(x−y)`, `g = 2R·1_{B̄_{2R}} + 1_{B̄₁}|log|·||`): `|p(x)||p(y)| ≤ p(x)² + p(y)²`
and Tonelli. This is the step "`logCov ψ̃ψ̃ ≤ ‖ψ̃‖₂² · sup_x ∫_K |log|x−y|| dy` (Schur test)" of the
plan in `handoff/P2-MKD.md`; own elementary proof (standard Schur test, e.g. Folland, *Real
Analysis*, Thm 6.18).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace MarkovGermVer

/-- the dominating translation kernel `g = 2R·1_{B̄_{2R}} + 1_{B̄₁}|log|·||` -/
def schurKer (R : ℝ) (z : ℂ) : ℝ :=
  (closedBall (0 : ℂ) (2 * R)).indicator (fun _ => 2 * R) z + logBallFun z

lemma schurKer_nonneg {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : 0 ≤ schurKer R z :=
  add_nonneg (indicator_nonneg (fun _ _ => by positivity) _) (logBallFun_nonneg z)

@[fun_prop] lemma measurable_logBallFun : Measurable logBallFun :=
  (continuous_abs.measurable.comp (Real.measurable_log.comp measurable_norm)).indicator
    measurableSet_closedBall

@[fun_prop] lemma measurable_schurKer (R : ℝ) : Measurable (schurKer R) :=
  (measurable_const.indicator measurableSet_closedBall).add measurable_logBallFun

lemma integrable_schurKer (R : ℝ) : Integrable (schurKer R) :=
  ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)).add integrable_logBallFun

lemma integral_schurKer {R : ℝ} (hR : 0 ≤ R) :
    ∫ z, schurKer R z = 2 * R * (Real.pi * (2 * R) ^ 2) + logBallConst := by
  unfold schurKer
  rw [integral_add ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)) integrable_logBallFun,
    integral_indicator measurableSet_closedBall, setIntegral_const, integral_logBallFun]
  simp only [smul_eq_mul, measureReal_def, volume_closedBall_toReal _ (by positivity : (0:ℝ) ≤ 2 * R)]
  ring

lemma abs_log_le_schurKer {R : ℝ} (hR : 0 ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |Real.log ‖x - y‖| ≤ schurKer R (x - y) := by
  have h2 : ‖x - y‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  unfold schurKer
  rw [indicator_of_mem (mem_closedBall_zero_iff.2 h2)]
  linarith [abs_log_norm_le (x - y)]

/-- **Schur bound** `logCov p p ≤ 2 L_R ∫ p²`. -/
theorem logCov_self_le_schur {p : ℂ → ℝ} {R : ℝ} (hR : 0 ≤ R) (hp : Continuous p)
    (hpR : ∀ x, R < ‖x‖ → p x = 0) :
    logCov p p ≤ 2 * (2 * R * (Real.pi * (2 * R) ^ 2) + logBallConst) * ∫ x, p x ^ 2 := by
  set L := 2 * R * (Real.pi * (2 * R) ^ 2) + logBallConst
  have hpc : HasCompactSupport p :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => hpR x (by simpa using hx)
  have hp2 : Integrable fun x => p x ^ 2 :=
    (hp.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 R)
      fun x hx => by simp [hpR x (by simpa using hx)])
  have hpm : Measurable fun x => ‖p x‖ₑ := hp.measurable.enorm
  have hpt : ∀ x y, ‖p x * (-Real.log ‖x - y‖) * p y‖ₑ ≤
      ‖p x‖ₑ ^ 2 * ‖schurKer R (x - y)‖ₑ + ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2 := by
    intro x y
    by_cases hx : ‖x‖ ≤ R
    · by_cases hy : ‖y‖ ≤ R
      · rw [enorm_mul, enorm_mul, enorm_neg]
        have hk : ‖Real.log ‖x - y‖‖ₑ ≤ ‖schurKer R (x - y)‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (schurKer_nonneg hR _)]
          exact ENNReal.ofReal_le_ofReal (abs_log_le_schurKer hR hx hy)
        calc ‖p x‖ₑ * ‖Real.log ‖x - y‖‖ₑ * ‖p y‖ₑ ≤ ‖p x‖ₑ * ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ := by
              gcongr
          _ = ‖schurKer R (x - y)‖ₑ * (‖p x‖ₑ * ‖p y‖ₑ) := by ring
          _ ≤ ‖schurKer R (x - y)‖ₑ * (‖p x‖ₑ ^ 2 + ‖p y‖ₑ ^ 2) := by
              gcongr
              rcases le_total ‖p x‖ₑ ‖p y‖ₑ with hle | hle
              · calc ‖p x‖ₑ * ‖p y‖ₑ ≤ ‖p y‖ₑ * ‖p y‖ₑ := by gcongr
                  _ ≤ _ := by rw [← sq]; exact le_add_self
              · calc ‖p x‖ₑ * ‖p y‖ₑ ≤ ‖p x‖ₑ * ‖p x‖ₑ := by gcongr
                  _ ≤ _ := by rw [← sq]; exact le_self_add
          _ = _ := by ring
      · rw [hpR y (not_le.1 hy)]; simp
    · rw [hpR x (not_le.1 hx)]; simp
  have h1 : ‖logCov p p‖ₑ ≤ ∫⁻ x, ∫⁻ y,
      (‖p x‖ₑ ^ 2 * ‖schurKer R (x - y)‖ₑ + ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2) := by
    unfold logCov
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => hpt x y)
  have hG : ∫⁻ z, ‖schurKer R z‖ₑ = ENNReal.ofReal L := by
    rw [show L = ∫ z, schurKer R z from (integral_schurKer hR).symm,
      ofReal_integral_eq_lintegral_ofReal (integrable_schurKer R)
      (ae_of_all _ (schurKer_nonneg hR))]
    exact lintegral_congr fun z => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (schurKer_nonneg hR z)]
  have hP : ∫⁻ x, ‖p x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, p x ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hp2 (ae_of_all _ fun x => sq_nonneg _)]
    exact lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h2 : ∫⁻ x, ∫⁻ y, (‖p x‖ₑ ^ 2 * ‖schurKer R (x - y)‖ₑ + ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2) =
      2 * ENNReal.ofReal L * ENNReal.ofReal (∫ x, p x ^ 2) := by
    have e1 : ∀ x, ∫⁻ y, (‖p x‖ₑ ^ 2 * ‖schurKer R (x - y)‖ₑ + ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2) =
        ‖p x‖ₑ ^ 2 * ENNReal.ofReal L + ∫⁻ y, ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2 := by
      intro x
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
        lintegral_sub_left_eq_self (fun z => ‖schurKer R z‖ₑ) x, hG]
    simp_rw [e1]
    rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop), hP,
      lintegral_lintegral_swap (by fun_prop)]
    have e2 : ∀ y, ∫⁻ x, ‖schurKer R (x - y)‖ₑ * ‖p y‖ₑ ^ 2 = ENNReal.ofReal L * ‖p y‖ₑ ^ 2 := by
      intro y
      rw [lintegral_mul_const _ (by fun_prop), lintegral_sub_right_eq_self (fun z => ‖schurKer R z‖ₑ) y,
        hG]
    simp_rw [e2]
    rw [lintegral_const_mul _ (by fun_prop), hP]
    ring
  rw [h2] at h1
  have hL0 : 0 ≤ L := by
    have := logBallConst_nonneg; positivity
  have hI0 : 0 ≤ ∫ x, p x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h3 : |logCov p p| ≤ 2 * L * ∫ x, p x ^ 2 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    simpa using h1
  exact (le_abs_self _).trans h3

end MarkovGermVer
end LQGMetric
