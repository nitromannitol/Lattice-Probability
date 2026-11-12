import Mathlib

/-!
# Circle-average Gaussian multiplicative chaos at two nearby radii

For a weight `g` and two radii `s, s' > 0`, the recentred circle-average approximations
`I_s(g) = ∫ g(z) s^{γ²/2} e^{γ (h_s(z) - H₀)} dz` at the two radii differ by at most a factor `e^t - 1` of the mass
`∫ |g(z)| s'^{γ²/2} e^{γ (h_{s'}(z) - H₀)} dz` at the second radius, where
`t = (γ²/2) |log s - log s'| + |γ| η` and `η` bounds `|h_s(z) - h_{s'}(z)|` on the support of `g`.

This is the deterministic step that turns a modulus of continuity of the circle-average process in the radius into
control of the approximations at every radius between the points of a finite grid of radii.

## Main results

* `abs_sub_le_of_abs_log_sub_le`: `|x - y| ≤ (e^t - 1) y` for `x, y > 0` with `|log x - log y| ≤ t`.
* `abs_integral_mul_sub_le`: the integrated form, for positive densities `F, G` against a weight `g`.
* `abs_integral_recentred_sub_le`: the comparison of the recentred approximations at radii `s` and `s'`.
-/

namespace LatticeProb.LQG.GMCScaleSandwich

open MeasureTheory Real

theorem abs_exp_sub_one_le_exp_abs_sub_one (d : ℝ) : |exp d - 1| ≤ exp |d| - 1 := by
  rcases le_or_gt 0 d with hd | hd
  · rw [abs_of_nonneg hd, abs_of_nonneg (by linarith [one_le_exp hd])]
  · rw [abs_of_neg hd, abs_of_nonpos (by linarith [Real.exp_lt_one_iff.2 hd])]
    linarith [add_one_le_exp d, add_one_le_exp (-d)]

/-- Two positive reals whose logarithms differ by at most `t` differ by at most `(e^t - 1)` times the second. -/
theorem abs_sub_le_of_abs_log_sub_le {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : |log x - log y| ≤ t) : |x - y| ≤ (exp t - 1) * y := by
  have hy0 : y ≠ 0 := hy.ne'
  have hd : x - y = y * (exp (log x - log y) - 1) := by
    rw [exp_sub, exp_log hx, exp_log hy]
    field_simp
  rw [hd, abs_mul, abs_of_pos hy, mul_comm (exp t - 1) y]
  refine mul_le_mul_of_nonneg_left ?_ hy.le
  calc |exp (log x - log y) - 1| ≤ exp |log x - log y| - 1 := abs_exp_sub_one_le_exp_abs_sub_one _
    _ ≤ exp t - 1 := by gcongr

/-- **Integrated comparison.** If the positive densities `F` and `G` have logarithms within `t` of each other on the
support of the weight `g`, then `|∫ g F - ∫ g G| ≤ (e^t - 1) ∫ |g| G`. -/
theorem abs_integral_mul_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g F G : α → ℝ} {t : ℝ}
    (hF : ∀ z, 0 < F z) (hG : ∀ z, 0 < G z) (h : ∀ z, g z ≠ 0 → |log (F z) - log (G z)| ≤ t)
    (hFi : Integrable (fun z => g z * F z) μ) (hGi : Integrable (fun z => g z * G z) μ) :
    |∫ z, g z * F z ∂μ - ∫ z, g z * G z ∂μ| ≤ (exp t - 1) * ∫ z, |g z| * G z ∂μ := by
  have hGa : Integrable (fun z => |g z| * G z) μ :=
    hGi.abs.congr (ae_of_all _ fun z => by simp only [abs_mul, abs_of_pos (hG z)])
  rw [← integral_sub hFi hGi, ← integral_const_mul]
  calc |∫ z, (g z * F z - g z * G z) ∂μ| ≤ ∫ z, |g z * F z - g z * G z| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, (exp t - 1) * (|g z| * G z) ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (hGa.const_mul _)
          (ae_of_all _ fun z => ?_)
        show |g z * F z - g z * G z| ≤ (exp t - 1) * (|g z| * G z)
        rw [← mul_sub, abs_mul]
        by_cases hg : g z = 0
        · simp [hg]
        · calc |g z| * |F z - G z| ≤ |g z| * ((exp t - 1) * G z) :=
                mul_le_mul_of_nonneg_left (abs_sub_le_of_abs_log_sub_le (hF z) (hG z) (h z hg))
                  (abs_nonneg _)
            _ = (exp t - 1) * (|g z| * G z) := by ring

/-- **Comparison of the recentred approximations at two radii.** For radii `s, s' > 0`, circle averages `hs`, `hs'`
at these radii with `|hs z - hs' z| ≤ η` on the support of `g`, and any recentring constant `H₀`,
`|I_s(g) - I_{s'}(g)| ≤ (e^{(γ²/2) |log s - log s'| + |γ| η} - 1) ∫ |g(z)| s'^{γ²/2} e^{γ (hs'(z) - H₀)} dz`. -/
theorem abs_integral_recentred_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {γ s s' η H₀ : ℝ}
    {g hs hs' : α → ℝ} (hs0 : 0 < s) (hs'0 : 0 < s') (hη : ∀ z, g z ≠ 0 → |hs z - hs' z| ≤ η)
    (hFi : Integrable (fun z => g z * (s ^ (γ ^ 2 / 2) * exp (γ * (hs z - H₀)))) μ)
    (hGi : Integrable (fun z => g z * (s' ^ (γ ^ 2 / 2) * exp (γ * (hs' z - H₀)))) μ) :
    |∫ z, g z * (s ^ (γ ^ 2 / 2) * exp (γ * (hs z - H₀))) ∂μ -
        ∫ z, g z * (s' ^ (γ ^ 2 / 2) * exp (γ * (hs' z - H₀))) ∂μ| ≤
      (exp (γ ^ 2 / 2 * |log s - log s'| + |γ| * η) - 1) *
        ∫ z, |g z| * (s' ^ (γ ^ 2 / 2) * exp (γ * (hs' z - H₀))) ∂μ := by
  refine abs_integral_mul_sub_le (fun z => by positivity) (fun z => by positivity) (fun z hz => ?_) hFi hGi
  rw [log_mul (rpow_pos_of_pos hs0 _).ne' (exp_pos _).ne', log_mul (rpow_pos_of_pos hs'0 _).ne' (exp_pos _).ne',
    log_exp, log_exp, log_rpow hs0, log_rpow hs'0]
  have hp : 0 ≤ γ ^ 2 / 2 := by positivity
  calc |γ ^ 2 / 2 * log s + γ * (hs z - H₀) - (γ ^ 2 / 2 * log s' + γ * (hs' z - H₀))|
      = |γ ^ 2 / 2 * (log s - log s') + γ * (hs z - hs' z)| := by ring_nf
    _ ≤ |γ ^ 2 / 2 * (log s - log s')| + |γ * (hs z - hs' z)| := abs_add_le _ _
    _ = γ ^ 2 / 2 * |log s - log s'| + |γ| * |hs z - hs' z| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp]
    _ ≤ γ ^ 2 / 2 * |log s - log s'| + |γ| * η := by
        gcongr
        exact hη z hz

end LatticeProb.LQG.GMCScaleSandwich
