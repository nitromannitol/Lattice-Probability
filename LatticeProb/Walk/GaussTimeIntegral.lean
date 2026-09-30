import Mathlib
import LatticeProb.Walk.ContinuousHeatGauss

/-!
# Time integrals of the continuous-time kernel and of its Gaussian counterpart

The Gamma integral `∫_0^∞ t^{-p} e^{-a/t} dt = Γ(p - 1) a^{1-p}` gives the time integral of
the Gaussian counterpart in dimension `d ≥ 3`, `2/((d - 2) ω_d) |x|^{2-d}` with `ω_d` the
volume of the unit ball (`integral_ctGauss`). The error of the local limit theorem integrates
over `t ≥ 1` to `O(|x|^{-d})` (`exists_norm_integral_ctHeat_sub_ctGauss_le`), and the times
`t ≤ 1` contribute `O(e^{-|x|/2})`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.ContinuousTime

variable {d : ℕ}

/-- The change-of-variable identity `x ^ (-2) • g (x ^ (-1)) = x ^ (p - 2) * exp (-(a * x))`
for `g t = t ^ (-p) * exp (-a / t)` and `x > 0`. -/
private lemma rpow_comp_rpow_eq {p a x : ℝ} (hx : 0 < x) :
    (|-1| * x ^ ((-1 : ℝ) - 1)) • ((x ^ (-1 : ℝ)) ^ (-p) * Real.exp (-a / x ^ (-1 : ℝ)))
      = x ^ (p - 2) * Real.exp (-(a * x)) := by
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
  simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one]
  rw [Real.inv_rpow hx0 (-p)]
  rw [Real.rpow_neg hx0 p]
  rw [inv_inv]
  rw [div_inv_eq_mul]
  rw [show ((-1 : ℝ) - 1) = -2 by norm_num]
  rw [smul_eq_mul, ← mul_assoc, ← Real.rpow_add hx (-2) p]
  rw [show (-2 : ℝ) + p = p - 2 by ring]
  rw [show -a * x = -(a * x) by ring]

/-- The integrand `t^{-p} e^{-a/t}` is integrable on `(0, ∞)` for `p > 1`, `a > 0`. -/
theorem integrableOn_rpow_neg_mul_exp_neg_div {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-a / t)) (Set.Ioi 0) := by
  have hp' : (-1 : ℝ) ≠ 0 := by norm_num
  have hbase : IntegrableOn (fun x : ℝ => x ^ (p - 2) * Real.exp (-(a * x))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := p - 2) (b := a)
      (by linarith) (le_refl 1) ha
    simpa only [Real.rpow_one, neg_mul] using h
  have hsub : IntegrableOn
      (fun x : ℝ => (|-1| * x ^ ((-1 : ℝ) - 1))
        • ((x ^ (-1 : ℝ)) ^ (-p) * Real.exp (-a / x ^ (-1 : ℝ)))) (Set.Ioi 0) :=
    hbase.congr_fun (fun x hx => (rpow_comp_rpow_eq hx).symm) measurableSet_Ioi
  exact (integrableOn_Ioi_comp_rpow_iff
    (fun t : ℝ => t ^ (-p) * Real.exp (-a / t)) (p := (-1 : ℝ)) hp').mp hsub

/-- The Gamma integral `∫_0^∞ t^{-p} e^{-a/t} dt = Γ(p - 1) a^{1-p}`, by the substitution
`t = 1/u`. -/
theorem integral_rpow_neg_mul_exp_neg_div {p a : ℝ} (hp : 1 < p) (ha : 0 < a) :
    ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-a / t) = Real.Gamma (p - 1) * a ^ (1 - p) := by
  have hp' : (-1 : ℝ) ≠ 0 := by norm_num
  have hpt : 0 < p - 1 := by linarith
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ => t ^ (-p) * Real.exp (-a / t))
    (p := (-1 : ℝ)) hp'
  have hcongr : (∫ x in Set.Ioi 0,
        (|-1| * x ^ ((-1 : ℝ) - 1))
          • ((x ^ (-1 : ℝ)) ^ (-p) * Real.exp (-a / x ^ (-1 : ℝ))))
      = ∫ x in Set.Ioi 0, x ^ (p - 2) * Real.exp (-(a * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    exact rpow_comp_rpow_eq hx
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p - 1) (r := a) hpt ha
  have hgamma' : (∫ x in Set.Ioi 0, x ^ (p - 2) * Real.exp (-(a * x)))
      = (1 / a) ^ (p - 1) * Real.Gamma (p - 1) := by
    rw [show p - 2 = (p - 1) - 1 by ring]
    exact hgamma
  have hcoef : (1 / a) ^ (p - 1) = a ^ (1 - p) := by
    rw [one_div, Real.inv_rpow ha.le]
    rw [← Real.rpow_neg ha.le, neg_sub]
  calc ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-a / t)
      = ∫ x in Set.Ioi 0,
          (|-1| * x ^ ((-1 : ℝ) - 1))
            • ((x ^ (-1 : ℝ)) ^ (-p) * Real.exp (-a / x ^ (-1 : ℝ))) := hsub.symm
    _ = ∫ x in Set.Ioi 0, x ^ (p - 2) * Real.exp (-(a * x)) := hcongr
    _ = (1 / a) ^ (p - 1) * Real.Gamma (p - 1) := hgamma'
    _ = Real.Gamma (p - 1) * a ^ (1 - p) := by rw [hcoef]; ring

/-- The Euclidean norm of a nonzero site is positive. -/
theorem euclidNorm_pos {x : Site d} (hx : x ≠ 0) : 0 < euclidNorm x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : (0 : ℝ) < ((x i : ℤ) : ℝ) ^ 2 := by
    have : ((x i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le hi' (Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℤ) : ℝ))
    (Finset.mem_univ i))

/-- In dimension `d ≥ 3` the Gaussian counterpart is integrable in time at a nonzero site. -/
theorem integrableOn_ctGauss (hd : 3 ≤ d) {x : Site d} (hx : x ≠ 0) :
    IntegrableOn (fun t => ctGauss d t x) (Set.Ioi 0) := by
  have hr := euclidNorm_pos hx
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : (1 : ℝ) < (d : ℝ) / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h : IntegrableOn (fun t : ℝ => (2 * Real.pi / d) ^ (-(d : ℝ) / 2)
      * (t ^ (-((d : ℝ) / 2)) * Real.exp (-(d * euclidNorm x ^ 2 / 2) / t))) (Set.Ioi 0) :=
    (integrableOn_rpow_neg_mul_exp_neg_div hp
      (show 0 < (d : ℝ) * euclidNorm x ^ 2 / 2 by positivity)).const_mul _
  exact IntegrableOn.congr_fun h (fun t ht => (ctGauss_eq (by omega) ht x).symm)
    measurableSet_Ioi

/-- **The constant of the Green function**:
`∫_0^∞ ḡ_t(x) dt = 2/((d - 2) ω_d) |x|^{2-d}`, `ω_d` the volume of the unit ball. -/
theorem integral_ctGauss (hd : 3 ≤ d) {x : Site d} (hx : x ≠ 0) :
    ∫ t in Set.Ioi 0, ctGauss d t x
      = 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
          * euclidNorm x ^ (2 - (d : ℝ)) := by
  have hr := euclidNorm_pos hx
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hp : (1 : ℝ) < (d : ℝ) / 2 := by linarith
  set r := euclidNorm x with hrdef
  have ha : 0 < (d : ℝ) * r ^ 2 / 2 := by positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => ctGauss_eq (by omega) ht x),
    integral_const_mul, integral_rpow_neg_mul_exp_neg_div hp ha]
  -- the volume of the unit ball
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hball : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      = Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
    rw [EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    ring
  have hG : Real.Gamma ((d : ℝ) / 2 + 1)
      = (d : ℝ) / 2 * (((d : ℝ) / 2 - 1) * Real.Gamma ((d : ℝ) / 2 - 1)) := by
    rw [Real.Gamma_add_one (by positivity)]
    congr 1
    rw [← Real.Gamma_add_one (by linarith)]
    congr 1
    ring
  have hGpos : 0 < Real.Gamma ((d : ℝ) / 2 - 1) := Real.Gamma_pos_of_pos (by linarith)
  rw [hball, hG]
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith
  have hpipos := Real.pi_pos
  -- compare through logarithms
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hpipos]
  have hlog1 : Real.log (2 * Real.pi / d) = Real.log 2 + Real.log Real.pi - Real.log d := by
    rw [Real.log_div (by positivity) hdpos.ne', Real.log_mul (by norm_num) hpipos.ne']
  have hlog2 : Real.log ((d : ℝ) * r ^ 2 / 2) = Real.log d + 2 * Real.log r - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul hdpos.ne' (by positivity),
      Real.log_pow]
    push_cast
    ring
  rw [hlog1, hlog2]
  have hd2' : (d : ℝ) / 2 = Real.exp (Real.log d - Real.log 2) := by
    rw [Real.exp_sub, Real.exp_log hdpos, Real.exp_log (by norm_num)]
  have key : Real.exp ((Real.log 2 + Real.log Real.pi - Real.log d) * (-(d : ℝ) / 2))
      * Real.exp ((Real.log d + 2 * Real.log r - Real.log 2) * (1 - (d : ℝ) / 2))
      = Real.exp (Real.log d - Real.log 2) * (Real.exp (Real.log Real.pi * ((d : ℝ) / 2)))⁻¹
        * Real.exp (Real.log r * (2 - (d : ℝ))) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexpne : Real.exp (Real.log Real.pi * ((d : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  calc Real.exp ((Real.log 2 + Real.log Real.pi - Real.log d) * (-(d : ℝ) / 2))
        * (Real.Gamma ((d : ℝ) / 2 - 1)
          * Real.exp ((Real.log d + 2 * Real.log r - Real.log 2) * (1 - (d : ℝ) / 2)))
      = Real.Gamma ((d : ℝ) / 2 - 1)
          * (Real.exp ((Real.log 2 + Real.log Real.pi - Real.log d) * (-(d : ℝ) / 2))
            * Real.exp ((Real.log d + 2 * Real.log r - Real.log 2) * (1 - (d : ℝ) / 2))) := by
        ring
    _ = _ := by
        rw [key, ← hd2']
        field_simp

/-- The error integrand `t^{-p} exp(-c r²/(t + r))` is integrable on `(1, ∞)` for `p > 1`. -/
theorem integrableOn_Ioi_one_rpow_mul_exp {p c r : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r))) (Set.Ioi 1) := by
  have hp' : -p < -1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r)))
      (Set.Ioi 1) := by
    have hinner : ContinuousOn (fun t : ℝ => -c * r ^ 2 / (t + r)) (Set.Ioi 1) := by
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.add continuousOn_const
      · intro t ht
        have : 1 < t := Set.mem_Ioi.mp ht
        positivity
    exact (continuousOn_id.rpow_const (fun t ht => Or.inl (by
      have h : 1 < t := Set.mem_Ioi.mp ht
      positivity))).mul (Real.continuous_exp.comp_continuousOn hinner)
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hp' zero_lt_one)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht' : 1 < t := Set.mem_Ioi.mp ht
  have ht0 : 0 < t := by linarith
  have htr : 0 < t + r := by linarith
  have hexp_le : Real.exp (-c * r ^ 2 / (t + r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hc (sq_nonneg r)]) htr.le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_nonneg _))]
  calc t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r)) ≤ t ^ (-p) * 1 :=
        mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg ht0.le _)
    _ = t ^ (-p) := mul_one _

/-- For `u > 0`, `u ^ (d / 2) * e ^ (-u) ≤ 1 + d!`. -/
private lemma rpow_half_mul_exp_neg_le {u : ℝ} (hu : 0 < u) (d : ℕ) :
    u ^ ((d : ℝ) / 2) * Real.exp (-u) ≤ 1 + (Nat.factorial d : ℝ) := by
  have hu0 : 0 ≤ u := hu.le
  have h_half : u ^ ((d : ℝ) / 2) ≤ 1 + u ^ (d : ℝ) := by
    rcases le_total u 1 with hu1 | hu1
    · have h1 : u ^ ((d : ℝ) / 2) ≤ 1 := Real.rpow_le_one hu0 hu1 (by positivity)
      have h2 : 0 ≤ u ^ (d : ℝ) := Real.rpow_nonneg hu0 _
      linarith
    · have h1 : u ^ ((d : ℝ) / 2) ≤ u ^ (d : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hu1 (by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith)
      linarith
  have h_exp : Real.exp (-u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h_d : u ^ (d : ℝ) * Real.exp (-u) ≤ (Nat.factorial d : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := u) hu0 d
    have hd : (0 : ℝ) < (Nat.factorial d : ℝ) := by positivity
    rw [div_le_iff₀ hd] at h
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos u), Real.rpow_natCast u d]
    nlinarith [h, Real.exp_pos u]
  calc u ^ ((d : ℝ) / 2) * Real.exp (-u)
      ≤ (1 + u ^ (d : ℝ)) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h_half (Real.exp_pos _).le
    _ = Real.exp (-u) + u ^ (d : ℝ) * Real.exp (-u) := by ring
    _ ≤ 1 + (Nat.factorial d : ℝ) := by linarith

/-- For `u > 0`, `e ^ (-u) ≤ u ^ (-(d / 2)) * (1 + d!)`. -/
private lemma exp_neg_le_rpow_neg_mul {u : ℝ} (hu : 0 < u) (d : ℕ) :
    Real.exp (-u) ≤ u ^ (-((d : ℝ) / 2)) * (1 + (Nat.factorial d : ℝ)) := by
  have h := rpow_half_mul_exp_neg_le hu d
  have hp : 0 < u ^ (-((d : ℝ) / 2)) := Real.rpow_pos_of_pos hu _
  have hone : u ^ (-((d : ℝ) / 2)) * u ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hu, show -((d : ℝ) / 2) + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  calc Real.exp (-u) = (u ^ (-((d : ℝ) / 2)) * u ^ ((d : ℝ) / 2)) * Real.exp (-u) := by
        rw [hone, one_mul]
    _ = u ^ (-((d : ℝ) / 2)) * (u ^ ((d : ℝ) / 2) * Real.exp (-u)) := by ring
    _ ≤ u ^ (-((d : ℝ) / 2)) * (1 + (Nat.factorial d : ℝ)) :=
        mul_le_mul_of_nonneg_left h hp.le

/-- The Gaussian counterpart is `O(|x|^{-d})` uniformly in time. -/
theorem exists_ctGauss_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : Site d, x ≠ 0 →
      ctGauss d t x ≤ C * euclidNorm x ^ (-(d : ℝ)) := by
  refine ⟨(2 * Real.pi / d) ^ (-(d : ℝ) / 2) * ((d : ℝ) / 2) ^ (-((d : ℝ) / 2))
      * (1 + (Nat.factorial d : ℝ)), ?_, ?_⟩
  · have h1 : 0 < (2 * Real.pi / d) ^ (-(d : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h2 : 0 < ((d : ℝ) / 2) ^ (-((d : ℝ) / 2)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h3 : 0 < 1 + (Nat.factorial d : ℝ) := by positivity
    positivity
  · intro t ht x hx
    have hxpos : 0 < euclidNorm x := euclidNorm_pos hx
    set a : ℝ := d * euclidNorm x ^ 2 / 2 with ha
    have hapos : 0 < a := by rw [ha]; positivity
    set u : ℝ := (d * euclidNorm x ^ 2 / 2) / t with hu
    have hupos : 0 < u := by rw [hu]; positivity
    have hu_eq : u = a / t := by rw [hu, ha]
    have htu : t * u = a := by rw [hu_eq]; field_simp
    have hexp_arg : -(d * euclidNorm x ^ 2 / 2) / t = -u := by
      rw [neg_div, ← hu]
    have hexp := exp_neg_le_rpow_neg_mul hupos d
    have hstep : t ^ (-((d : ℝ) / 2)) * Real.exp (-u)
        ≤ a ^ (-((d : ℝ) / 2)) * (1 + (Nat.factorial d : ℝ)) := by
      calc t ^ (-((d : ℝ) / 2)) * Real.exp (-u)
          ≤ t ^ (-((d : ℝ) / 2))
              * (u ^ (-((d : ℝ) / 2)) * (1 + (Nat.factorial d : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le _)
        _ = (t ^ (-((d : ℝ) / 2)) * u ^ (-((d : ℝ) / 2)))
              * (1 + (Nat.factorial d : ℝ)) := by ring
        _ = a ^ (-((d : ℝ) / 2)) * (1 + (Nat.factorial d : ℝ)) := by
            rw [← Real.mul_rpow ht.le hupos.le, htu]
    have hfac : a ^ (-((d : ℝ) / 2))
        = ((d : ℝ) / 2) ^ (-((d : ℝ) / 2)) * euclidNorm x ^ (-(d : ℝ)) := by
      have haeq : a = ((d : ℝ) / 2) * euclidNorm x ^ 2 := by rw [ha]; ring
      rw [haeq, Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast (euclidNorm x) 2, ← Real.rpow_mul hxpos.le]
      congr 1
      ring
    rw [ctGauss_eq hd ht x, hexp_arg]
    calc (2 * Real.pi / d) ^ (-(d : ℝ) / 2)
          * (t ^ (-((d : ℝ) / 2)) * Real.exp (-u))
        ≤ (2 * Real.pi / d) ^ (-(d : ℝ) / 2) * (a ^ (-((d : ℝ) / 2))
            * (1 + (Nat.factorial d : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg (by positivity) _)
      _ = (2 * Real.pi / d) ^ (-(d : ℝ) / 2)
            * (((d : ℝ) / 2) ^ (-((d : ℝ) / 2))
              * euclidNorm x ^ (-(d : ℝ)) * (1 + (Nat.factorial d : ℝ))) := by rw [hfac]
      _ = ((2 * Real.pi / d) ^ (-(d : ℝ) / 2) * ((d : ℝ) / 2) ^ (-((d : ℝ) / 2))
            * (1 + (Nat.factorial d : ℝ))) * euclidNorm x ^ (-(d : ℝ)) := by ring

/-- Pointwise bound for the shifted exponential: for `t > 1` and `r ≥ 1` the
exponent `-c r²/(t+r)` is controlled by a constant term and a `1/t` term. -/
private lemma exp_neg_div_add_le {c r t : ℝ} (hc : 0 < c) (hr : 1 ≤ r) (ht : 1 < t) :
    Real.exp (-c * r ^ 2 / (t + r))
      ≤ Real.exp (-c * r / 2) + Real.exp (-(c / 2) * r ^ 2 / t) := by
  have hr0 : 0 < r := by linarith
  have ht0 : 0 < t := by linarith
  have htr0 : 0 < t + r := by positivity
  rcases le_or_gt t r with htr | htr
  · have hle : c * r ^ 2 / (t + r) ≥ c * r / 2 := by
      have h2 : c * r ^ 2 / (2 * r) ≤ c * r ^ 2 / (t + r) :=
        div_le_div_of_nonneg_left (by positivity) htr0 (by linarith)
      have h3 : c * r ^ 2 / (2 * r) = c * r / 2 := by
        field_simp
      linarith
    have hexp : Real.exp (-c * r ^ 2 / (t + r)) ≤ Real.exp (-c * r / 2) := by
      apply Real.exp_le_exp.mpr
      rw [show -c * r ^ 2 / (t + r) = -(c * r ^ 2 / (t + r)) by ring_nf,
        show -c * r / 2 = -(c * r / 2) by ring_nf, neg_le_neg_iff]
      exact hle
    linarith [Real.exp_nonneg (-(c / 2) * r ^ 2 / t)]
  · have hle : c * r ^ 2 / (t + r) ≥ (c / 2) * r ^ 2 / t := by
      have h2 : c * r ^ 2 / (2 * t) ≤ c * r ^ 2 / (t + r) :=
        div_le_div_of_nonneg_left (by positivity) htr0 (by linarith)
      have h3 : c * r ^ 2 / (2 * t) = (c / 2) * r ^ 2 / t := by
        field_simp
      linarith
    have hexp : Real.exp (-c * r ^ 2 / (t + r)) ≤ Real.exp (-(c / 2) * r ^ 2 / t) := by
      apply Real.exp_le_exp.mpr
      rw [show -c * r ^ 2 / (t + r) = -(c * r ^ 2 / (t + r)) by ring_nf,
        show -(c / 2) * r ^ 2 / t = -((c / 2) * r ^ 2 / t) by ring_nf, neg_le_neg_iff]
      exact hle
    linarith [Real.exp_nonneg (-c * r / 2)]

/-- Splits the integral over `Ioi 1` into a constant multiple of `∫ t^(-p)` plus
a tail integral over `Ioi 0`. -/
private lemma integral_le_split {p c r : ℝ} (hp : 1 < p) (hc : 0 < c) (hr : 1 ≤ r) :
    ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r))
      ≤ Real.exp (-c * r / 2) * (∫ t in Set.Ioi 1, t ^ (-p))
        + ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t) := by
  have hr0 : 0 < r := by linarith
  have hA : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r)))
      (Set.Ioi 1) := integrableOn_Ioi_one_rpow_mul_exp hp hc.le hr0.le
  have hB0 : IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num : (0 : ℝ) < 1)
  have hB : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-c * r / 2)) (Set.Ioi 1) :=
    hB0.mul_const (Real.exp (-c * r / 2))
  have hC : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t))
      (Set.Ioi 0) := by
    simpa only [neg_mul] using
      integrableOn_rpow_neg_mul_exp_neg_div hp (by positivity : 0 < (c / 2) * r ^ 2)
  have hC1 : IntegrableOn (fun t : ℝ => t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t))
      (Set.Ioi 1) := hC.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hmono : ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r))
      ≤ ∫ t in Set.Ioi 1,
          (t ^ (-p) * Real.exp (-c * r / 2) + t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t)) := by
    apply setIntegral_mono_on hA (hB.add hC1) measurableSet_Ioi
    intro t ht
    have ht1 : 1 < t := ht
    calc
      t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r))
          ≤ t ^ (-p) * (Real.exp (-c * r / 2) + Real.exp (-(c / 2) * r ^ 2 / t)) :=
            mul_le_mul_of_nonneg_left (exp_neg_div_add_le hc hr ht1)
              (Real.rpow_nonneg (by linarith) _)
      _ = t ^ (-p) * Real.exp (-c * r / 2)
            + t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t) := by ring_nf
  have hadd : ∫ t in Set.Ioi 1,
        (t ^ (-p) * Real.exp (-c * r / 2) + t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t))
      = (∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r / 2))
        + ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t) :=
    integral_add hB hC1
  have hconst : ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r / 2)
      = Real.exp (-c * r / 2) * (∫ t in Set.Ioi 1, t ^ (-p)) := by
    rw [integral_mul_const]
    ring_nf
  have hle0 : ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t)
      ≤ ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t) := by
    apply setIntegral_mono_set hC
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
    · filter_upwards with t ht
      exact zero_lt_one.trans ht
  linarith [hmono, hle0, hconst, hadd]

/-- There is `K > 0` with `exp (-c r/2) ≤ K r^(2-2p)` for all `r ≥ 1`. -/
private lemma exists_exp_neg_le_mul_rpow (p c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧
      ∀ r : ℝ, 1 ≤ r → Real.exp (-c * r / 2) ≤ K * r ^ (2 - 2 * p) := by
  let m : ℕ := Nat.ceil (2 * p - 2)
  refine ⟨(m.factorial : ℝ) * (2 / c) ^ m, ?_, ?_⟩
  · positivity
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hm : 2 * p - 2 ≤ (m : ℝ) := Nat.le_ceil (2 * p - 2)
    have hrpow : r ^ (2 * p - 2) ≤ r ^ m := by
      have h := Real.rpow_le_rpow_of_exponent_le hr hm
      simpa only [Real.rpow_natCast] using h
    have hfac : r ^ m ≤ (m.factorial : ℝ) * (2 / c) ^ m * Real.exp (c * r / 2) := by
      have hx : 0 ≤ c * r / 2 := by positivity
      have h1 : (c * r / 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (c * r / 2) := by
        have h := Real.pow_div_factorial_le_exp (c * r / 2) hx m
        have h' : (c * r / 2) ^ m ≤ Real.exp (c * r / 2) * (m.factorial : ℝ) := by
          rwa [div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))] at h
        calc
          (c * r / 2) ^ m ≤ Real.exp (c * r / 2) * (m.factorial : ℝ) := h'
          _ = (m.factorial : ℝ) * Real.exp (c * r / 2) := by ring_nf
      have h2 : (c * r / 2) ^ m = (c / 2) ^ m * r ^ m := by
        rw [show c * r / 2 = (c / 2) * r by ring_nf, mul_pow]
      rw [h2] at h1
      have h3 : (2 / c) ^ m * ((c / 2) ^ m * r ^ m) = r ^ m := by
        rw [← mul_assoc, ← mul_pow, show 2 / c * (c / 2) = 1 by field_simp, one_pow, one_mul]
      calc
        r ^ m = (2 / c) ^ m * ((c / 2) ^ m * r ^ m) := h3.symm
        _ ≤ (2 / c) ^ m * ((m.factorial : ℝ) * Real.exp (c * r / 2)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (m.factorial : ℝ) * (2 / c) ^ m * Real.exp (c * r / 2) := by ring_nf
    have hexp_bound : r ^ (2 * p - 2) * Real.exp (-c * r / 2)
        ≤ (m.factorial : ℝ) * (2 / c) ^ m := by
      have hexp1 : Real.exp (c * r / 2) * Real.exp (-c * r / 2) = 1 := by
        rw [← Real.exp_add, show c * r / 2 + (-c * r / 2) = 0 by ring_nf, Real.exp_zero]
      calc
        r ^ (2 * p - 2) * Real.exp (-c * r / 2)
            ≤ r ^ m * Real.exp (-c * r / 2) :=
              mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
        _ ≤ ((m.factorial : ℝ) * (2 / c) ^ m * Real.exp (c * r / 2))
              * Real.exp (-c * r / 2) :=
              mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
        _ = (m.factorial : ℝ) * (2 / c) ^ m := by
              rw [mul_assoc, mul_assoc, hexp1, mul_one]
    have hmul : r ^ (2 * p - 2) * r ^ (2 - 2 * p) = 1 := by
      rw [← Real.rpow_add hr0, show 2 * p - 2 + (2 - 2 * p) = 0 by ring_nf, Real.rpow_zero]
    have hrew : Real.exp (-c * r / 2)
        = r ^ (2 * p - 2) * Real.exp (-c * r / 2) * r ^ (2 - 2 * p) := by
      rw [show r ^ (2 * p - 2) * Real.exp (-c * r / 2) * r ^ (2 - 2 * p)
            = (r ^ (2 * p - 2) * r ^ (2 - 2 * p)) * Real.exp (-c * r / 2) by ring_nf,
        hmul, one_mul]
    rw [hrew]
    exact mul_le_mul_of_nonneg_right hexp_bound (Real.rpow_nonneg hr0.le _)

/-- The integral `∫_{t>1} t^(-p)` equals `1/(p-1)` for `p > 1`. -/
private lemma integral_Ioi_one_rpow_neg (p : ℝ) (hp : 1 < p) :
    ∫ t in Set.Ioi 1, t ^ (-p) = 1 / (p - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num : (0 : ℝ) < 1)]
  rw [Real.one_rpow]
  field_simp
  rw [show (-p + 1 : ℝ) = -(p - 1) by ring_nf, div_neg, neg_neg]

/-- Evaluation of the tail integral `∫_{t>0} t^(-p) exp (-(c/2) r²/t)`. -/
private lemma integral_Ioi_zero_rpow_neg_exp (p c r : ℝ) (hp : 1 < p) (hc : 0 < c)
    (hr0 : 0 < r) :
    ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t)
      = Real.Gamma (p - 1) * ((c / 2) * r ^ 2) ^ (1 - p) := by
  simpa only [neg_mul] using
    integral_rpow_neg_mul_exp_neg_div hp (by positivity : 0 < (c / 2) * r ^ 2)

/-- Splits the `(1-p)`-power of the product `(c/2) r²`. -/
private lemma quarter_rpow_eq (p c r : ℝ) (hc : 0 < c) (hr0 : 0 < r) :
    ((c / 2) * r ^ 2) ^ (1 - p) = (c / 2) ^ (1 - p) * r ^ (2 - 2 * p) := by
  rw [Real.mul_rpow (by positivity) (sq_nonneg r)]
  rw [← Real.rpow_natCast r 2]
  rw [← Real.rpow_mul hr0.le]
  congr 1
  ring_nf

/-- The error integral: `∫_1^∞ t^{-p} exp(-c r²/(t + r)) dt ≤ C r^{2-2p}` for `r ≥ 1`. -/
theorem exists_integral_Ioi_one_rpow_mul_exp_le {p c : ℝ} (hp : 1 < p) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r)) ≤ C * r ^ (2 - 2 * p) := by
  obtain ⟨K, hKpos, hK⟩ := exists_exp_neg_le_mul_rpow p c hc
  have hGpos : 0 < Real.Gamma (p - 1) := Real.Gamma_pos_of_pos (by linarith)
  have hc2pos : 0 < (c / 2) ^ (1 - p) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨K / (p - 1) + Real.Gamma (p - 1) * (c / 2) ^ (1 - p), ?_, ?_⟩
  · have h1 : 0 < K / (p - 1) := div_pos hKpos (by linarith)
    have h2 : 0 < Real.Gamma (p - 1) * (c / 2) ^ (1 - p) := mul_pos hGpos hc2pos
    linarith
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hsplit := integral_le_split hp hc hr
    have hint1 : ∫ t in Set.Ioi 1, t ^ (-p) = 1 / (p - 1) := integral_Ioi_one_rpow_neg p hp
    have hint2 : ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t)
        = Real.Gamma (p - 1) * ((c / 2) * r ^ 2) ^ (1 - p) :=
      integral_Ioi_zero_rpow_neg_exp p c r hp hc hr0
    have hpow := quarter_rpow_eq p c r hc hr0
    have hK' := hK r hr
    have h1 : Real.exp (-c * r / 2) * (1 / (p - 1))
        ≤ K * r ^ (2 - 2 * p) * (1 / (p - 1)) :=
      mul_le_mul_of_nonneg_right hK' (by positivity)
    calc
      ∫ t in Set.Ioi 1, t ^ (-p) * Real.exp (-c * r ^ 2 / (t + r))
          ≤ Real.exp (-c * r / 2) * (∫ t in Set.Ioi 1, t ^ (-p))
              + ∫ t in Set.Ioi 0, t ^ (-p) * Real.exp (-(c / 2) * r ^ 2 / t) := hsplit
      _ = Real.exp (-c * r / 2) * (1 / (p - 1))
              + Real.Gamma (p - 1) * ((c / 2) * r ^ 2) ^ (1 - p) := by rw [hint1, hint2]
      _ ≤ K * r ^ (2 - 2 * p) * (1 / (p - 1))
              + Real.Gamma (p - 1) * (c / 2) ^ (1 - p) * r ^ (2 - 2 * p) := by
            rw [hpow]
            exact add_le_add h1 (le_of_eq (by ring_nf))
      _ = (K / (p - 1) + Real.Gamma (p - 1) * (c / 2) ^ (1 - p)) * r ^ (2 - 2 * p) := by
            ring_nf

/-- `e^{-r/2} ≤ 2ⁿ n! r^{-n}` for `r > 0`. -/
theorem exp_neg_half_le_rpow {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Real.exp (-r / 2) ≤ 2 ^ n * n.factorial * r ^ (-(n : ℝ)) := by
  have h := Real.pow_div_factorial_le_exp (x := r / 2) (by positivity) n
  have hpos : 0 < (r / 2) ^ n / n.factorial := by positivity
  calc Real.exp (-r / 2) = 1 / Real.exp (r / 2) := by rw [neg_div, Real.exp_neg, one_div]
    _ ≤ 1 / ((r / 2) ^ n / n.factorial) := one_div_le_one_div_of_le hpos h
    _ = 2 ^ n * n.factorial * r ^ (-(n : ℝ)) := by
        rw [Real.rpow_neg hr.le, Real.rpow_natCast, div_pow]; field_simp

/-- The kernel difference `q_t(x) - ḡ_t(x)` is integrable in time on `(1, ∞)`. -/
theorem integrableOn_ctHeat_sub_ctGauss (hd : 1 ≤ d) (x : Site d) :
    IntegrableOn (fun t => ctHeat d t x - ctGauss d t x) (Set.Ioi 1) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := exists_abs_ctHeat_sub_ctGauss_le hd
  have hp1 : (1 : ℝ) < ((d : ℝ) + 2) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine Integrable.mono'
    ((integrableOn_Ioi_one_rpow_mul_exp hp1 hc₁.le (euclidNorm_nonneg x)).const_mul C₁) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_))
  · exact ((continuous_ctHeat x).aestronglyMeasurable).sub
      (((continuousOn_ctGauss x).mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi)
  · rw [Real.norm_eq_abs]
    refine (h₁ t (le_of_lt ht) x).trans (le_of_eq ?_)
    rw [neg_div]
    ring

/-- The large-time error: `|∫_1^∞ (q_t(x) - ḡ_t(x)) dt| ≤ C |x|^{-d}` for `|x| ≥ 1`. -/
theorem exists_norm_integral_ctHeat_sub_ctGauss_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Site d, 1 ≤ euclidNorm x →
      ‖∫ t in Set.Ioi 1, (ctHeat d t x - ctGauss d t x)‖
        ≤ C * euclidNorm x ^ (-(d : ℝ)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := exists_abs_ctHeat_sub_ctGauss_le hd
  set p : ℝ := ((d : ℝ) + 2) / 2 with hp
  have hp1 : 1 < p := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hp]; linarith
  obtain ⟨C₂, hC₂, h₂⟩ := exists_integral_Ioi_one_rpow_mul_exp_le hp1 hc₁
  refine ⟨C₁ * C₂, by positivity, fun x hx => ?_⟩
  set r := euclidNorm x with hr
  set B : ℝ → ℝ := fun t => C₁ * (t ^ (-p) * Real.exp (-c₁ * r ^ 2 / (t + r))) with hB
  have hBint : IntegrableOn B (Set.Ioi 1) :=
    (integrableOn_Ioi_one_rpow_mul_exp hp1 hc₁.le (euclidNorm_nonneg x)).const_mul C₁
  have hbig : ∀ t ∈ Set.Ioi (1 : ℝ), ‖ctHeat d t x - ctGauss d t x‖ ≤ B t := by
    intro t ht
    rw [Real.norm_eq_abs]
    refine (h₁ t (le_of_lt ht) x).trans (le_of_eq ?_)
    rw [hB, hp, neg_div]
    ring
  refine (norm_integral_le_of_norm_le hBint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall hbig))).trans ?_
  rw [hB, integral_const_mul, mul_assoc]
  gcongr
  refine (h₂ r hx).trans (le_of_eq ?_)
  congr 2
  rw [hp]
  ring

/-- The small-time contribution: `|∫_0^1 q_t(x) dt| ≤ e · e^{-|x|/2}`. -/
theorem norm_integral_Ioc_ctHeat_le (hd : 1 ≤ d) (x : Site d) :
    ‖∫ t in Set.Ioc 0 1, ctHeat d t x‖ ≤ Real.exp 1 * Real.exp (-euclidNorm x / 2) := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
    (f := fun t => ctHeat d t x) (C := Real.exp 1 * Real.exp (-euclidNorm x / 2))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun t ht => by
      rw [Real.norm_eq_abs]
      refine (abs_ctHeat_le hd ht.1.le x).trans ?_
      gcongr
      exact ht.2)
  simpa [Measure.real, Real.volume_Ioc] using h

end LatticeProb.ContinuousTime
