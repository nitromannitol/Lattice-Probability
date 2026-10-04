/-
Step F of the Bernstein route: the deterministic real-analysis integration of the
sub-exponential (Bernstein) conditional mgf bound `exp (-t² / (2 (v + a t)))` to the
`r`-th absolute moment,

  `∫_0^∞ r t^{r-1} exp (-t²/(2(v+at))) dt ≤ K^r (r^{r/2} v^{r/2} + (r a)^r)`,

with a universal constant `K`.  The pointwise split

  `exp (-t²/(2(v+at))) ≤ exp (-t²/(4v)) + exp (-t/(4a))`

(one branch per side of `a t = v`) reduces the bound to a Gaussian moment and an
exponential moment, both evaluated by Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`; the only asymptotic input is `Γ(x) ≤ x^x` for
`x ≥ 1`.
-/
import Mathlib
import LatticeProb.Prob.Freedman

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- Euler's Gamma function grows at most like `x ^ x` for `x ≥ 1`. -/
theorem Gamma_le_self_rpow {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ x ^ x := by
  by_cases hx2 : x ≤ 2
  · -- `1 ≤ x ≤ 2`: on the interior log-convexity against `Γ 1 = Γ 2 = 1`, at the
    -- endpoints directly.
    rcases eq_or_lt_of_le hx with rfl | hx1lt
    · norm_num [Real.Gamma_one]
    rcases eq_or_lt_of_le hx2 with rfl | hx2lt
    · norm_num [Real.Gamma_two]
    · have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
        (s := 1) (t := 2) (a := 2 - x) (b := x - 1)
        (by norm_num) (by norm_num) (by linarith) (by linarith) (by ring_nf)
      have harg : (2 - x) * 1 + (x - 1) * 2 = x := by ring_nf
      rw [harg, Real.Gamma_one, Real.Gamma_two, Real.one_rpow, Real.one_rpow,
        mul_one] at hconv
      exact hconv.trans (Real.one_le_rpow hx (by positivity))
  · -- `x > 2`: `Γ x ≤ Γ (⌊x⌋+1) = ⌊x⌋! ≤ ⌊x⌋^⌊x⌋ ≤ x ^ x`.
    have hx2' : 2 < x := lt_of_not_ge hx2
    set n : ℕ := ⌊x⌋₊ with hn
    have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ x by linarith))
    have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith : (0 : ℝ) ≤ x)
    have hxlt : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmem : (2 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (2 : ℕ) ≤ n + 1 := by omega
      exact_mod_cast this
    have hmono : Real.Gamma x ≤ Real.Gamma ((n : ℝ) + 1) :=
      le_of_lt (Real.Gamma_strictMonoOn_Ici
        (show x ∈ Ici (2 : ℝ) by exact_mod_cast (show (2 : ℝ) ≤ x by linarith))
        (show ((n : ℝ) + 1) ∈ Ici (2 : ℝ) by exact hmem) hxlt)
    rw [Real.Gamma_nat_eq_factorial n] at hmono
    have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have hpow : (n : ℝ) ^ n ≤ x ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) hnx n
    have hpowx : x ^ (n : ℝ) ≤ x ^ x :=
      Real.rpow_le_rpow_of_exponent_le hx (by exact_mod_cast hnx)
    linarith

/-- The coefficient estimate `r · 2^{r-1} ≤ 16^r` for `r ≥ 2`. -/
private theorem mul_two_pow_pred_le (r : ℝ) (hr : 2 ≤ r) : r * 2 ^ (r - 1) ≤ 16 ^ r := by
  have hr0 : 0 ≤ r := by linarith
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h2 : (2 : ℝ) ^ (r - 1) ≤ 2 ^ r :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h1 : r * 2 ^ (r - 1) ≤ Real.exp r * 2 ^ r :=
    mul_le_mul hre h2 (by positivity) (Real.exp_pos r).le
  have h2e : Real.exp r * 2 ^ r = (2 * Real.exp 1) ^ r := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_nonneg 1)]
    rw [show Real.exp 1 ^ r = Real.exp r by rw [← Real.exp_mul]; ring_nf]
    ring_nf
  rw [h2e] at h1
  refine h1.trans ?_
  exact Real.rpow_le_rpow (by positivity) (by have := Real.exp_one_lt_three; linarith) hr0

/-- The coefficient estimate `r · 4^r ≤ 16^r` for `r ≥ 2`. -/
private theorem mul_four_rpow_le (r : ℝ) (hr : 2 ≤ r) : r * 4 ^ r ≤ 16 ^ r := by
  have hr0 : 0 ≤ r := by linarith
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h1 : r * 4 ^ r ≤ Real.exp r * 4 ^ r :=
    mul_le_mul_of_nonneg_right hre (by positivity)
  have h4e : Real.exp r * 4 ^ r = (4 * Real.exp 1) ^ r := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg 1)]
    rw [show Real.exp 1 ^ r = Real.exp r by rw [← Real.exp_mul]; ring_nf]
    ring_nf
  rw [h4e] at h1
  refine h1.trans ?_
  exact Real.rpow_le_rpow (by positivity) (by have := Real.exp_one_lt_three; linarith) hr0

/-- The Gaussian moment `∫_0^∞ r t^{r-1} exp (-t²/(4v)) ≤ 16^r r^{r/2} v^{r/2}`. -/
private theorem integral_gaussian_moment_le (r v : ℝ) (hr : 2 ≤ r) (hv : 0 < v) :
    ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
      ≤ 16 ^ r * (r ^ (r / 2) * v ^ (r / 2)) := by
  have hr1 : -1 < r - 1 := by linarith
  have hb : (0 : ℝ) < 1 / (4 * v) := by positivity
  have hval := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := r - 1) (b := 1 / (4 * v))
    (by norm_num) hr1 hb
  have hval' : ∫ x in Ioi (0 : ℝ), x ^ (r - 1) * Real.exp (-(1 / (4 * v)) * x ^ 2)
      = (1 / (4 * v)) ^ (-(r - 1 + 1) / 2) * (1 / 2) * Real.Gamma ((r - 1 + 1) / 2) := by
    simpa [Real.rpow_natCast] using hval
  have hcongr : (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))))
      = fun t : ℝ => r * (t ^ (r - 1) * Real.exp (-(1 / (4 * v)) * t ^ 2)) := by
    funext t
    rw [show t ^ 2 / (4 * v) = (1 / (4 * v)) * t ^ 2 by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hGval : ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
      = r * ((1 / (4 * v)) ^ (-(r - 1 + 1) / 2) * (1 / 2)
          * Real.Gamma ((r - 1 + 1) / 2)) := by
    rw [hcongr, MeasureTheory.integral_const_mul]
    rw [hval']
  have hconst : (1 / (4 * v)) ^ (-(r - 1 + 1) / 2) = 2 ^ r * v ^ (r / 2) := by
    rw [show -(r - 1 + 1) / 2 = -(r / 2) by ring_nf]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 / (4 * v)), one_div,
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 * v), inv_inv]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hv.le]
    have h4 : (4 : ℝ) ^ (r / 2) = 2 ^ r := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
        ← Real.rpow_mul (x := 2) (y := 2) (z := r / 2) (by norm_num)]
      congr 1
      ring_nf
    rw [h4]
  have hgam : Real.Gamma ((r - 1 + 1) / 2) ≤ r ^ (r / 2) := by
    rw [show (r - 1 + 1) / 2 = r / 2 by ring_nf]
    refine (Gamma_le_self_rpow (show (1 : ℝ) ≤ r / 2 by linarith)).trans ?_
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have htwo : (2 : ℝ) ^ r * (1 / 2) = 2 ^ (r - 1) := by
    rw [show (1 : ℝ) / 2 = 2 ^ (-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
  have hcoef : r * (2 ^ r * (1 / 2)) ≤ 16 ^ r := by
    rw [htwo]
    exact mul_two_pow_pred_le r hr
  rw [hGval]
  calc r * ((1 / (4 * v)) ^ (-(r - 1 + 1) / 2) * (1 / 2) * Real.Gamma ((r - 1 + 1) / 2))
      = r * (2 ^ r * v ^ (r / 2) * (1 / 2) * Real.Gamma ((r - 1 + 1) / 2)) := by
        rw [hconst]
    _ ≤ r * (2 ^ r * v ^ (r / 2) * (1 / 2) * r ^ (r / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hgam (by positivity)
    _ = (r * (2 ^ r * (1 / 2))) * (r ^ (r / 2) * v ^ (r / 2)) := by ring_nf
    _ ≤ 16 ^ r * (r ^ (r / 2) * v ^ (r / 2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- The exponential moment `∫_0^∞ r t^{r-1} exp (-t/(4a)) ≤ 16^r (r a)^r`. -/
private theorem integral_exp_moment_le (r a : ℝ) (hr : 2 ≤ r) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t / (4 * a)))
      ≤ 16 ^ r * (r * a) ^ r := by
  have hr1 : -1 < r - 1 := by linarith
  have hb : (0 : ℝ) < 1 / (4 * a) := by positivity
  have hval := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := r - 1) (b := 1 / (4 * a))
    (by norm_num) hr1 hb
  have hval' : ∫ x in Ioi (0 : ℝ), x ^ (r - 1) * Real.exp (-(1 / (4 * a)) * x)
      = (1 / (4 * a)) ^ (-(r - 1 + 1) / 1) * (1 / 1) * Real.Gamma ((r - 1 + 1) / 1) := by
    simpa [Real.rpow_one] using hval
  have hcongr : (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t / (4 * a))))
      = fun t : ℝ => r * (t ^ (r - 1) * Real.exp (-(1 / (4 * a)) * t)) := by
    funext t
    rw [show t / (4 * a) = (1 / (4 * a)) * t by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hEval : ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t / (4 * a)))
      = r * ((1 / (4 * a)) ^ (-(r - 1 + 1) / 1) * (1 / 1)
          * Real.Gamma ((r - 1 + 1) / 1)) := by
    rw [hcongr, MeasureTheory.integral_const_mul]
    rw [hval']
  have hconst : (1 / (4 * a)) ^ (-(r - 1 + 1) / 1) = (4 * a) ^ r := by
    rw [show -(r - 1 + 1) / 1 = -r by ring_nf]
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 / (4 * a)), one_div,
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 * a), inv_inv]
  have hgam : Real.Gamma r ≤ r ^ r := by
    rw [show r = (r - 1 + 1) / 1 by ring_nf]
    exact Gamma_le_self_rpow (by linarith)
  have hcoef : r * 4 ^ r ≤ 16 ^ r := mul_four_rpow_le r hr
  rw [hEval, hconst]
  rw [div_one, mul_one]
  rw [show (r - 1 + 1) / 1 = r by ring_nf]
  calc r * ((4 * a) ^ r * Real.Gamma r)
      ≤ r * ((4 * a) ^ r * r ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left hgam (by positivity)
    _ = (r * 4 ^ r) * (r * a) ^ r := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ha.le,
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ r) ha.le]
        ring_nf
    _ ≤ 16 ^ r * (r * a) ^ r := mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- **Step F.**  The deterministic Bernstein integral: integrating the sub-exponential
tail `exp (-t²/(2(v+at)))` against `r t^{r-1}` is at most `16^r` times
`r^{r/2} v^{r/2} + (r a)^r`. -/
theorem integral_rpow_exp_bernstein (r a v : ℝ) (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v) :
    ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
      ≤ 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) := by
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
        ≤ r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
          + r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hcoef : 0 ≤ r * t ^ (r - 1) := by positivity
    by_cases h : a * t ≤ v
    · have hexp : -(t ^ 2 / (2 * (v + a * t))) ≤ -(t ^ 2 / (4 * v)) := by
        apply neg_le_neg
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * v)
          (by positivity : (0 : ℝ) < 2 * (v + a * t))]
        nlinarith [h, sq_nonneg t]
      have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hcoef
      have h2 : 0 ≤ r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) := by positivity
      linarith
    · have h' : v < a * t := lt_of_not_ge h
      have hle : t ^ 2 / (4 * a * t) ≤ t ^ 2 / (2 * (v + a * t)) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * a * t)
          (by positivity : (0 : ℝ) < 2 * (v + a * t))]
        nlinarith [h', sq_nonneg t, ht0.le]
      have h2t : t ^ 2 / (4 * a * t) = t / (4 * a) := by
        field_simp
      have hexp : -(t ^ 2 / (2 * (v + a * t))) ≤ -(t / (4 * a)) := by
        rw [← h2t]
        exact neg_le_neg hle
      have h1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hcoef
      have h3 : 0 ≤ r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))) := by positivity
      linarith
  have hGint : IntegrableOn (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))))
      (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(1 / (4 * v)) * t ^ 2))
        (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / (4 * v)) (by positivity) (by linarith)
    refine (MeasureTheory.Integrable.const_mul h0 r).congr ?_
    filter_upwards with t
    rw [show t ^ 2 / (4 * v) = (1 / (4 * v)) * t ^ 2 by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hEint : IntegrableOn (fun t : ℝ => r * t ^ (r - 1) * Real.exp (-(t / (4 * a))))
      (Ioi 0) := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(1 / (4 * a)) * t))
        (Ioi 0) := by
      simpa [Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (s := r - 1) (p := 1) (b := 1 / (4 * a))
          (by linarith) (by norm_num) (by positivity)
    refine (MeasureTheory.Integrable.const_mul h0 r).congr ?_
    filter_upwards with t
    rw [show t / (4 * a) = (1 / (4 * a)) * t by
      rw [div_eq_mul_inv, one_div]; ring_nf]
    ring_nf
  have hGEint : IntegrableOn (fun t : ℝ =>
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
        + r * t ^ (r - 1) * Real.exp (-(t / (4 * a)))) (Ioi 0) := hGint.add hEint
  have hFint : IntegrableOn (fun t : ℝ =>
      r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))) (Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hGEint ?_ ?_
    · fun_prop
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have htpos : 0 < t ^ (r - 1) := Real.rpow_pos_of_pos ht _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpoint t ht
  have hInt := MeasureTheory.setIntegral_mono_on hFint hGEint measurableSet_Ioi hpoint
  have hsplit : ∫ t in Ioi (0 : ℝ),
        (r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v)))
          + r * t ^ (r - 1) * Real.exp (-(t / (4 * a))))
      = (∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))))
        + ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) :=
    MeasureTheory.integral_add hGint hEint
  rw [hsplit] at hInt
  have hG := integral_gaussian_moment_le r v hr hv
  have hE := integral_exp_moment_le r a hr ha
  calc ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
      ≤ (∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (4 * v))))
          + ∫ t in Ioi (0 : ℝ), r * t ^ (r - 1) * Real.exp (-(t / (4 * a))) := hInt
    _ ≤ 16 ^ r * (r ^ (r / 2) * v ^ (r / 2)) + 16 ^ r * (r * a) ^ r := add_le_add hG hE
    _ = 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) := by ring_nf

/-- **Step F, two-sided companion.**  The same integral with the prefactor `2`,
which is what a two-sided tail `P(|M| ≥ t)` produces. -/
theorem integral_rpow_exp_bernstein_two_sided (r a v : ℝ) (hr : 2 ≤ r) (ha : 0 < a)
    (hv : 0 < v) :
    ∫ t in Ioi (0 : ℝ), 2 * r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
      ≤ 2 * 16 ^ r * (r ^ (r / 2) * v ^ (r / 2) + (r * a) ^ r) := by
  have h := integral_rpow_exp_bernstein r a v hr ha hv
  have hcongr : ∫ t in Ioi (0 : ℝ),
        2 * r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t))))
      = 2 * ∫ t in Ioi (0 : ℝ),
          r * t ^ (r - 1) * Real.exp (-(t ^ 2 / (2 * (v + a * t)))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    ring_nf
  rw [hcongr]
  linarith [h]

end LatticeProb
