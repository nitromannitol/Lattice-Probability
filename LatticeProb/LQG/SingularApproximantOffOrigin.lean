import LatticeProb.LQG.LQGMeasure
import LatticeProb.Gauss.CircleAverageApprox
import LatticeProb.LQG.AnnularBallPowerInterpolation

/-!
# Singular approximants away from the logarithmic singularity

For a field with a logarithmic singularity `h = h₀ - α log |·|`, the circle average at
scale `ε > 0` is `h₀_ε(x) - α log max(ε, |x|)` (Jensen's formula). Hence the approximant
`lqgApprox γ (fieldCircleAverage α h₀) ε` has density `max(ε, |x|) ^ (-γ α)` with respect to
the approximant `lqgApprox γ h₀ ε` of the regular field.

When `γ α ≥ 0` and `2 r ≤ |z|`, every point of `ball z r` has modulus at least `|z| / 2`, so
the singular approximant of `ball z r` is at most `(|z| / 2) ^ (-γ α)` times the regular
approximant of the same ball. A power bound `C r ^ κ` for the regular approximant therefore
gives the off-origin bound `2 ^ (γ α) C |z| ^ (-γ α) r ^ κ`, and together with a power bound
at the origin, `ball_le_ofReal_rpow_of_origin_of_offOrigin` yields a power bound for every
ball of radius at most one in a compact set.
-/

open MeasureTheory Metric

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- Jensen's formula for the logarithmically shifted circle average: at scale `ε > 0`,
`h_ε(x) = h₀_ε(x) - α log max(ε, |x|)`. -/
theorem fieldCircleAverage_eq_sub_log_max (α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : ℂ) :
    fieldCircleAverage α hcirc ε x = hcirc ε x - α * Real.log (max ε ‖x‖) := by
  have h := circleAverage_log_norm_sub_eq_log_max hε x 0
  simp only [sub_zero] at h
  simp only [fieldCircleAverage, h]

/-- The approximation density of the singular field is the regular approximation density
times `max(ε, |x|) ^ (-γ α)`. -/
theorem approxDensity_fieldCircleAverage_eq (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (x : ℂ) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hcirc ε x) =
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x) * max ε ‖x‖ ^ (-(γ * α)) := by
  have hM : 0 < max ε ‖x‖ := lt_of_lt_of_le hε (le_max_left _ _)
  rw [fieldCircleAverage_eq_sub_log_max α hcirc hε, Real.rpow_def_of_pos hM, mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

/-- Pointwise comparison of approximation densities at points of modulus at least `d > 0`,
when `γ α ≥ 0`. -/
theorem approxDensity_fieldCircleAverage_le (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hγα : 0 ≤ γ * α) {d : ℝ} (hd : 0 < d) {x : ℂ} (hx : d ≤ ‖x‖) :
    ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hcirc ε x)) ≤
      ENNReal.ofReal (d ^ (-(γ * α))) *
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
  apply ENNReal.ofReal_le_ofReal
  rw [approxDensity_fieldCircleAverage_eq γ α hcirc hε x]
  have hle : max ε ‖x‖ ^ (-(γ * α)) ≤ d ^ (-(γ * α)) :=
    Real.rpow_le_rpow_of_nonpos hd (le_trans hx (le_max_right _ _)) (neg_nonpos.2 hγα)
  have hpos : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  calc ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x) * max ε ‖x‖ ^ (-(γ * α))
      ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x) * d ^ (-(γ * α)) :=
        mul_le_mul_of_nonneg_left hle hpos
    _ = d ^ (-(γ * α)) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ε x)) := by ring

/-- **Singular approximants of balls away from the singularity.** If `γ α ≥ 0` and
`2 r ≤ |z|` with `z ≠ 0`, the singular approximant of `ball z r` is at most
`(|z| / 2) ^ (-γ α)` times the regular approximant of `ball z r`. -/
theorem lqgApprox_fieldCircleAverage_ball_le (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hγα : 0 ≤ γ * α) {z : ℂ} {r : ℝ} (hz : 0 < ‖z‖) (hzr : 2 * r ≤ ‖z‖) :
    lqgApprox γ (fieldCircleAverage α hcirc) ε (ball z r) ≤
      ENNReal.ofReal ((‖z‖ / 2) ^ (-(γ * α))) * lqgApprox γ hcirc ε (ball z r) := by
  unfold lqgApprox
  rw [withDensity_apply _ measurableSet_ball, withDensity_apply _ measurableSet_ball,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono_ae' measurableSet_ball (ae_of_all _ fun x hx => ?_)
  refine approxDensity_fieldCircleAverage_le γ α hcirc hε hγα (half_pos hz) ?_
  rw [mem_ball, dist_eq_norm] at hx
  have h1 := norm_sub_norm_le z x
  rw [norm_sub_rev] at h1
  linarith

/-- `(d / 2) ^ (-g) = 2 ^ g d ^ (-g)` for `d ≥ 0`. -/
theorem half_rpow_neg_eq {d : ℝ} (hd : 0 ≤ d) (g : ℝ) :
    (d / 2) ^ (-g) = 2 ^ g * d ^ (-g) := by
  rw [Real.div_rpow hd zero_lt_two.le, Real.rpow_neg zero_lt_two.le, div_inv_eq_mul, mul_comm]

/-- **Off-origin power bound for singular approximants.** A power bound `C r ^ κ` for the
regular approximant of `ball z r` with `2 r ≤ |z|` gives the bound
`2 ^ (γ α) C |z| ^ (-γ α) r ^ κ` for the singular approximant. -/
theorem lqgApprox_fieldCircleAverage_ball_le_offOrigin (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (hγα : 0 ≤ γ * α) {C κ : ℝ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hzr : 2 * r ≤ ‖z‖)
    (hm : lqgApprox γ hcirc ε (ball z r) ≤ ENNReal.ofReal (C * r ^ κ)) :
    lqgApprox γ (fieldCircleAverage α hcirc) ε (ball z r) ≤
      ENNReal.ofReal (2 ^ (γ * α) * C * ‖z‖ ^ (-(γ * α)) * r ^ κ) := by
  have hz : 0 < ‖z‖ := by linarith
  have hw : 0 ≤ (‖z‖ / 2) ^ (-(γ * α)) := Real.rpow_nonneg (by positivity) _
  calc lqgApprox γ (fieldCircleAverage α hcirc) ε (ball z r)
      ≤ ENNReal.ofReal ((‖z‖ / 2) ^ (-(γ * α))) * lqgApprox γ hcirc ε (ball z r) :=
        lqgApprox_fieldCircleAverage_ball_le γ α hcirc hε hγα hz hzr
    _ ≤ ENNReal.ofReal ((‖z‖ / 2) ^ (-(γ * α))) * ENNReal.ofReal (C * r ^ κ) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (γ * α) * C * ‖z‖ ^ (-(γ * α)) * r ^ κ) := by
        rw [← ENNReal.ofReal_mul hw, half_rpow_neg_eq hz.le]
        congr 1
        ring

/-- **Ball power bound for singular approximants.** Let `γ α ≥ 0`. Suppose that the
singular approximant at scale `ε > 0` satisfies an origin bound `A s ^ a` on balls
`ball 0 s` with `s ≤ max 3 (3 R / 2)`, and that the regular approximant satisfies
`C r ^ κ` on every ball `ball z r` with `|z| ≤ R` and `0 < r ≤ 1`. Then the singular
approximant satisfies a power bound `K r ^ β` on every such ball, with
`β = min a (κ a / (a + γ α))`; the constant `K` depends only on `A, a, C, γ α`. -/
theorem lqgApprox_fieldCircleAverage_ball_le_rpow (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hγα : 0 ≤ γ * α) {R A C a κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : 0 < a)
    (horig : ∀ s : ℝ, 0 < s → s ≤ max 3 (3 / 2 * R) →
      lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 s) ≤ ENNReal.ofReal (A * s ^ a))
    (hm : ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      lqgApprox γ hcirc ε (ball z r) ≤ ENNReal.ofReal (C * r ^ κ)) :
    ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      lqgApprox γ (fieldCircleAverage α hcirc) ε (ball z r) ≤ ENNReal.ofReal
        (max (A * 3 ^ a)
            ((A * (3 / 2) ^ a) ^ (1 - a / (a + γ * α)) *
              (2 ^ (γ * α) * C) ^ (a / (a + γ * α))) *
          r ^ min a (κ * (a / (a + γ * α)))) :=
  ball_le_ofReal_rpow_of_origin_of_offOrigin _ hA
    (mul_nonneg (Real.rpow_nonneg zero_lt_two.le _) hC) ha hγα horig
    fun z hz r hr hr1 hzr =>
      lqgApprox_fieldCircleAverage_ball_le_offOrigin γ α hcirc hε hγα hr hzr.le
        (hm z hz r hr hr1)

end LatticeProb.LQG
