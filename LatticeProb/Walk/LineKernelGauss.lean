import Mathlib
import LatticeProb.Walk.LineKernel

/-!
# The Gaussian comparison for the one-dimensional continuous-time kernel

`lineGauss s k = (2πs)^{-1/2} e^{-k²/(2s)}` is the Gaussian of variance `s` at the integer `k`.
This module proves the ingredients of the local limit theorem for `lineKernel`
(`LatticeProb/Walk/LineKernelLocalLimit.lean`). The Gaussian integral along every horizontal
line `Im z = l` is computed exactly; on the line `Im z = l` with `|l| ≤ 1/2`, the lattice and
the Gaussian integrands differ by `O(s(θ⁴ + l⁴))` against a Gaussian in `θ`; and after the
contour shift, `2π(lineKernel s k - lineGauss s k)` splits into the integral of that
difference over `[-π, π]` and a Gaussian tail off `[-π, π]`, each bounded here.
-/

open MeasureTheory

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The Gaussian kernel of variance `s` at an integer, `(2πs)^{-1/2} e^{-k²/(2s)}`. -/
def lineGauss (s : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(k : ℝ) ^ 2 / (2 * s))

/-- The entire Gaussian integrand `z ↦ e^{-s z²/2 + ikz}`. -/
def gaussIntegrand (s : ℝ) (k : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-(s : ℂ) / 2 * z ^ 2 + (k : ℂ) * z * Complex.I)

/-- Rewrites `gaussIntegrand s k` at the vertically shifted argument `θ + l I`
as a complex quadratic exponential in `θ` with coefficients `b = -s/2`,
`c = k I - s l I` and `d = s l²/2 - k l`. -/
private lemma gaussIntegrand_shift_expand (s : ℝ) (k : ℤ) (l θ : ℝ) :
    gaussIntegrand s k (θ + l * Complex.I) =
      Complex.exp ((-(s : ℂ) / 2) * θ ^ 2 +
        ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I) * θ +
        ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))) := by
  simp only [gaussIntegrand]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The real part `-s/2` of the quadratic coefficient is negative when `s > 0`. -/
private lemma gaussIntegrand_neg_re {s : ℝ} (hs : 0 < s) :
    ((-(s : ℂ) / 2).re < 0) := by
  rw [show (-(s : ℂ) / 2) = (((-(s / 2)) : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re]
  linarith

/-- The shifted Gaussian exponent `d - c²/(4b)` simplifies to `-k²/(2s)`; the
`l`-terms cancel. -/
private lemma gauss_exponent_eq (s : ℝ) (hs : s ≠ 0) (k : ℤ) (l : ℝ) :
    ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ)) -
      ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I) ^ 2 /
        (4 * (-(s : ℂ) / 2)) = -(k : ℂ) ^ 2 / (2 * (s : ℂ)) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp [hsC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex Gaussian prefactor `(π / (s/2))^(1/2)` is the complex cast of
`Real.sqrt (2π/s)`. -/
private lemma gauss_coeff_sqrt (s : ℝ) (hs : 0 < s) :
    (Real.pi / (-( -(s : ℂ) / 2))) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 * Real.pi / s) : ℝ) : ℂ) := by
  have h1 : (-( -(s : ℂ) / 2)) = ((s / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_div]
  have h2 : Real.pi / (s / 2) = 2 * Real.pi / s := by
    field_simp
  rw [h2]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ 2 * Real.pi / s) (1/2 : ℝ)]
  rw [Real.sqrt_eq_rpow]

/-- The Gaussian integral value `√(2π/s) e^{-k²/(2s)}` equals `2π * lineGauss s k`. -/
private lemma lineGauss_coeff (s : ℝ) (hs : 0 < s) (k : ℤ) :
    ((Real.sqrt (2 * Real.pi / s) : ℝ) : ℂ) * Complex.exp (-(k : ℂ) ^ 2 / (2 * (s : ℂ))) =
      (2 * Real.pi : ℂ) * lineGauss s k := by
  have hpos1 : 0 ≤ 2 * Real.pi / s := by positivity
  have hpos2 : 0 < 2 * Real.pi * s := by positivity
  have hsq : Real.sqrt (2 * Real.pi / s) * Real.sqrt (2 * Real.pi * s) = 2 * Real.pi := by
    rw [← Real.sqrt_mul hpos1 (2 * Real.pi * s)]
    have hmul : (2 * Real.pi / s) * (2 * Real.pi * s) = (2 * Real.pi) ^ 2 := by
      field_simp
    rw [hmul, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hsqrt_ne : Real.sqrt (2 * Real.pi * s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos2)
  have hreal : Real.sqrt (2 * Real.pi / s) * Real.exp (-(k : ℝ) ^ 2 / (2 * s)) =
      (2 * Real.pi) * lineGauss s k := by
    rw [lineGauss]
    field_simp [Real.exp_ne_zero, hsqrt_ne]
    linarith
  have hexp : -(k : ℂ) ^ 2 / (2 * (s : ℂ)) = (((-(k : ℝ) ^ 2 / (2 * s)) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcexp : Complex.exp (-(k : ℂ) ^ 2 / (2 * (s : ℂ))) =
      ((Real.exp (-(k : ℝ) ^ 2 / (2 * s)) : ℝ) : ℂ) := by
    rw [hexp, ← Complex.ofReal_exp]
  rw [hcexp]
  rw [← Complex.ofReal_mul]
  rw [show (2 * Real.pi : ℂ) * ((lineGauss s k : ℝ) : ℂ) =
      ((2 * Real.pi * lineGauss s k : ℝ) : ℂ) by push_cast; ring]
  exact congrArg (fun x : ℝ => (x : ℂ)) hreal

/-- The Gaussian integrand integrates over every horizontal line `Im z = l` to `2π` times
the Gaussian kernel: the exponent is a complex quadratic in `θ`, and the `l`-terms cancel. -/
theorem integral_gaussIntegrand_shift {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    ∫ θ : ℝ, gaussIntegrand s k (θ + l * Complex.I)
      = (2 * Real.pi : ℂ) * lineGauss s k := by
  simp_rw [gaussIntegrand_shift_expand s k l]
  rw [integral_cexp_quadratic (gaussIntegrand_neg_re hs)
        ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I)
        ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))]
  rw [gauss_exponent_eq s (ne_of_gt hs) k l, gauss_coeff_sqrt s hs]
  exact lineGauss_coeff s hs k

/-- The Gaussian integrand is integrable along every horizontal line. -/
theorem integrable_gaussIntegrand_shift {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    Integrable fun θ : ℝ => gaussIntegrand s k (θ + l * Complex.I) := by
  simp_rw [gaussIntegrand_shift_expand s k l]
  exact integrable_cexp_quadratic' (gaussIntegrand_neg_re hs)
    ((k : ℂ) * Complex.I - (s : ℂ) * (l : ℂ) * Complex.I)
    ((s : ℂ) * (l : ℂ) ^ 2 / 2 - (k : ℂ) * (l : ℂ))

/-- The modulus of the Gaussian integrand on the line `Im z = l` is
`exp(-s(θ² - l²)/2 - k l)`. -/
theorem norm_gaussIntegrand_shift (s : ℝ) (k : ℤ) (θ l : ℝ) :
    ‖gaussIntegrand s k (θ + l * Complex.I)‖
      = Real.exp (-s * (θ ^ 2 - l ^ 2) / 2 - k * l) := by
  unfold gaussIntegrand
  rw [Complex.norm_exp]
  congr 1
  have hdiv : (-(s : ℂ)) / 2 = ((-(s / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdiv]
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

/-- The quartic Taylor bound `|cos w - 1 + w²/2| ≤ |w|⁴ e^{|w|}` for complex `w`, from the
two exponential series of `cos w = (e^{iw} + e^{-iw})/2`. -/
theorem norm_cos_sub_one_add_sq_le (w : ℂ) :
    ‖Complex.cos w - 1 + w ^ 2 / 2‖ ≤ ‖w‖ ^ 4 * Real.exp ‖w‖ := by
  have h2 : (w * Complex.I) ^ 2 = -w ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  have h3 : (w * Complex.I) ^ 3 = -w ^ 3 * Complex.I := by
    ring_nf
    rw [Complex.I_pow_three]
    ring
  have h2' : (-w * Complex.I) ^ 2 = -w ^ 2 := by
    rw [show -w * Complex.I = -(w * Complex.I) by ring, neg_sq]; exact h2
  have h3' : (-w * Complex.I) ^ 3 = w ^ 3 * Complex.I := by
    rw [show -w * Complex.I = -(w * Complex.I) by ring]
    ring_nf
    rw [Complex.I_pow_three]
    ring
  have hsum : (∑ m ∈ Finset.range 4, (w * Complex.I) ^ m / m.factorial
        + ∑ m ∈ Finset.range 4, (-w * Complex.I) ^ m / m.factorial) / 2 =
        1 - w ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    rw [h2, h3, h2', h3']
    ring
  have h : Complex.cos w - 1 + w ^ 2 / 2
      = ((Complex.exp (w * Complex.I)
            - ∑ m ∈ Finset.range 4, (w * Complex.I) ^ m / m.factorial)
        + (Complex.exp (-w * Complex.I)
            - ∑ m ∈ Finset.range 4, (-w * Complex.I) ^ m / m.factorial)) / 2 := by
    rw [Complex.cos]
    rw [show (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 - 1
          + w ^ 2 / 2
        = (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2
          - (1 - w ^ 2 / 2) by ring]
    rw [← hsum]
    ring
  rw [h]
  have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp (w * Complex.I) 4
  have h2b := Complex.norm_exp_sub_sum_le_norm_mul_exp (-w * Complex.I) 4
  have hw1 : ‖w * Complex.I‖ = ‖w‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hw2 : ‖-w * Complex.I‖ = ‖w‖ := by rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
  calc ‖((Complex.exp (w * Complex.I)
          - ∑ m ∈ Finset.range 4, (w * Complex.I) ^ m / m.factorial)
        + (Complex.exp (-w * Complex.I)
          - ∑ m ∈ Finset.range 4, (-w * Complex.I) ^ m / m.factorial)) / 2‖
      = ‖(Complex.exp (w * Complex.I)
            - ∑ m ∈ Finset.range 4, (w * Complex.I) ^ m / m.factorial)
          + (Complex.exp (-w * Complex.I)
            - ∑ m ∈ Finset.range 4, (-w * Complex.I) ^ m / m.factorial)‖ / 2 := by
        rw [norm_div]; norm_num
    _ ≤ (‖Complex.exp (w * Complex.I)
            - ∑ m ∈ Finset.range 4, (w * Complex.I) ^ m / m.factorial‖
          + ‖Complex.exp (-w * Complex.I)
            - ∑ m ∈ Finset.range 4, (-w * Complex.I) ^ m / m.factorial‖) / 2 := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (‖w * Complex.I‖ ^ 4 * Real.exp ‖w * Complex.I‖
          + ‖-w * Complex.I‖ ^ 4 * Real.exp ‖-w * Complex.I‖) / 2 := by
        gcongr
    _ = ‖w‖ ^ 4 * Real.exp ‖w‖ := by rw [hw1, hw2]; ring

/-- The mean value bound `|e^a - e^b| ≤ |a - b| max(e^{Re a}, e^{Re b})` along the segment
from `b` to `a`. -/
theorem norm_exp_sub_exp_le (a b : ℂ) :
    ‖Complex.exp a - Complex.exp b‖ ≤ ‖a - b‖ * max (Real.exp a.re) (Real.exp b.re) := by
  let f : ℝ → ℂ := fun t => Complex.exp (b + (t : ℂ) * (a - b))
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f
      (Complex.exp (b + (t : ℂ) * (a - b)) * (1 * (a - b)))
      (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t :=
      (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (a - b)) (1 * (a - b)) t :=
      h1.mul_const (a - b)
    have h3 : HasDerivAt (fun y : ℝ => b + (y : ℂ) * (a - b)) (1 * (a - b)) t :=
      h2.const_add b
    exact (h3.cexp).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖Complex.exp (b + (t : ℂ) * (a - b)) * (1 * (a - b))‖
        ≤ ‖a - b‖ * max (Real.exp a.re) (Real.exp b.re) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hre : (b + (t : ℂ) * (a - b)).re = b.re + t * (a.re - b.re) := by
      simp [Complex.add_re, Complex.mul_re, Complex.sub_re]
    have hexp_le : Real.exp (b.re + t * (a.re - b.re))
        ≤ max (Real.exp a.re) (Real.exp b.re) := by
      have hle : b.re + t * (a.re - b.re) ≤ max a.re b.re := by
        have h1 : (1 - t) * b.re ≤ (1 - t) * max a.re b.re :=
          mul_le_mul_of_nonneg_left (le_max_right a.re b.re) (by linarith)
        have h2 : t * a.re ≤ t * max a.re b.re :=
          mul_le_mul_of_nonneg_left (le_max_left a.re b.re) ht0
        nlinarith
      calc Real.exp (b.re + t * (a.re - b.re))
          ≤ Real.exp (max a.re b.re) := Real.exp_le_exp.mpr hle
        _ = max (Real.exp a.re) (Real.exp b.re) := Real.exp_monotone.map_max
    rw [one_mul, Complex.norm_mul, Complex.norm_exp, hre]
    calc Real.exp (b.re + t * (a.re - b.re)) * ‖a - b‖
        ≤ max (Real.exp a.re) (Real.exp b.re) * ‖a - b‖ :=
          mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
      _ = ‖a - b‖ * max (Real.exp a.re) (Real.exp b.re) := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f) hderiv hbound
  have hf1 : f 1 = Complex.exp a := by
    simp only [f]
    congr 1
    norm_num
  have hf0 : f 0 = Complex.exp b := by
    simp only [f]
    congr 1
    simp
  rwa [hf1, hf0] at key

/-- `cosh l - 1 ≤ (3/5) l²` for `|l| ≤ 1/2`. -/
theorem cosh_sub_one_le {l : ℝ} (hl : |l| ≤ 1 / 2) : Real.cosh l - 1 ≤ 3 / 5 * l ^ 2 := by
  have hl2 : l ^ 2 ≤ 1 / 4 := by
    have : l ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [sq_le_sq]
      simpa using hl
    norm_num at this
    exact this
  have hu_nn : 0 ≤ l ^ 2 / 2 := by positivity
  have hu_abs : |l ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg hu_nn]
    linarith
  have hexp := Real.abs_exp_sub_one_sub_id_le hu_abs
  have hx_le : Real.exp (l ^ 2 / 2) - 1 - l ^ 2 / 2 ≤ (l ^ 2 / 2) ^ 2 :=
    le_trans (le_abs_self _) hexp
  calc Real.cosh l - 1 ≤ Real.exp (l ^ 2 / 2) - 1 := by
        linarith [Real.cosh_le_exp_half_sq l]
    _ = (Real.exp (l ^ 2 / 2) - 1 - l ^ 2 / 2) + l ^ 2 / 2 := by ring
    _ ≤ (l ^ 2 / 2) ^ 2 + l ^ 2 / 2 := by linarith
    _ ≤ 3 / 5 * l ^ 2 := by nlinarith [hl2]

/-- The squared norm of `θ + l i` is `θ ^ 2 + l ^ 2`. -/
private lemma normSq_linePoint (θ l : ℝ) :
    ‖(θ : ℂ) + (l : ℂ) * Complex.I‖ ^ 2 = θ ^ 2 + l ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]

/-- `θ + l i` lies in the ball of radius `4` when `|θ| ≤ π` and `|l| ≤ 1 / 2`. -/
private lemma norm_linePoint_le_four {θ l : ℝ} (hθ : |θ| ≤ Real.pi) (hl : |l| ≤ 1 / 2) :
    ‖(θ : ℂ) + (l : ℂ) * Complex.I‖ ≤ 4 := by
  have hnorm := normSq_linePoint θ l
  have hθ' : θ ^ 2 ≤ Real.pi ^ 2 := by
    have h := abs_le.mp hθ
    nlinarith [h.1, h.2, Real.pi_pos]
  have hl' : l ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have h := abs_le.mp hl
    nlinarith [h.1, h.2]
  nlinarith [norm_nonneg ((θ : ℂ) + (l : ℂ) * Complex.I), hnorm, hθ', hl',
    Real.pi_lt_d2, Real.pi_pos]

/-- On `|θ| ≤ π` and `|l| ≤ 1 / 2`, the exponential of `‖θ + l i‖` is at most `55`. -/
private lemma exp_norm_linePoint_le {θ l : ℝ} (hθ : |θ| ≤ Real.pi) (hl : |l| ≤ 1 / 2) :
    Real.exp ‖(θ : ℂ) + (l : ℂ) * Complex.I‖ ≤ 55 := by
  have h4 := norm_linePoint_le_four hθ hl
  have hexp4 : Real.exp 4 < 55 := by
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul 1 4]
      norm_num
    rw [h]
    calc Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
          gcongr
          exact Real.exp_one_lt_d9
      _ < 55 := by norm_num
  exact (Real.exp_le_exp_of_le h4).trans hexp4.le

/-- `‖θ + l i‖ ^ 4 ≤ 2 (θ ^ 4 + l ^ 4)`. -/
private lemma norm_linePoint_pow_four_le (θ l : ℝ) :
    ‖(θ : ℂ) + (l : ℂ) * Complex.I‖ ^ 4 ≤ 2 * (θ ^ 4 + l ^ 4) := by
  have hnorm := normSq_linePoint θ l
  nlinarith [sq_nonneg (θ ^ 2 - l ^ 2), hnorm]

/-- Real part of the `lineIntegrand` exponent at `θ + l i`. -/
private lemma lineExp_re (s : ℝ) (k : ℤ) (θ l : ℝ) :
    (-(s : ℂ) * (1 - Complex.cos ((θ : ℂ) + (l : ℂ) * Complex.I))
        + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I).re
      = -s * (1 - Real.cos θ * Real.cosh l) - k * l := by
  rw [Complex.cos_add_mul_I]
  rw [← Complex.ofReal_cos]
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.sub_im]
  ring

/-- Real part of the `gaussIntegrand` exponent at `θ + l i`. -/
private lemma gaussExp_re (s : ℝ) (k : ℤ) (θ l : ℝ) :
    (-(s : ℂ) / 2 * ((θ : ℂ) + (l : ℂ) * Complex.I) ^ 2
        + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I).re
      = -(s * (θ ^ 2 - l ^ 2)) / 2 - k * l := by
  rw [pow_two]
  simp
  ring

/-- Bound on the real part of the `lineIntegrand` exponent. -/
private lemma lineExp_re_le (s : ℝ) (hs : 0 ≤ s) (k : ℤ) {θ l : ℝ} (hθ : |θ| ≤ Real.pi)
    (hl : |l| ≤ 1 / 2) :
    (-(s : ℂ) * (1 - Complex.cos ((θ : ℂ) + (l : ℂ) * Complex.I))
        + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I).re
      ≤ -(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2 := by
  rw [lineExp_re]
  have hcos : Real.cos θ ≤ 1 - 2 / Real.pi ^ 2 * θ ^ 2 := Real.cos_le_one_sub_mul_cos_sq hθ
  have hcosh1 : 1 ≤ Real.cosh l := Real.one_le_cosh l
  have hle : 2 / Real.pi ^ 2 * θ ^ 2 ≤ 1 - Real.cos θ := by nlinarith [hcos]
  have hnonneg : 0 ≤ 1 - Real.cos θ := by
    have : 0 ≤ 2 / Real.pi ^ 2 * θ ^ 2 := by positivity
    linarith
  have hA : 2 / Real.pi ^ 2 * θ ^ 2 ≤ (1 - Real.cos θ) * Real.cosh l := by
    calc 2 / Real.pi ^ 2 * θ ^ 2 = (2 / Real.pi ^ 2 * θ ^ 2) * 1 := by ring
      _ ≤ (1 - Real.cos θ) * Real.cosh l := mul_le_mul hle hcosh1 (by norm_num) hnonneg
  have hA0 : 0 ≤ (1 - Real.cos θ) * Real.cosh l - 2 / Real.pi ^ 2 * θ ^ 2 := by linarith
  have hB0 : 0 ≤ 3 / 5 * l ^ 2 - (Real.cosh l - 1) := by
    have h := cosh_sub_one_le hl
    linarith
  have hsum : 0 ≤ s * ((1 - Real.cos θ) * Real.cosh l - 2 / Real.pi ^ 2 * θ ^ 2
      + (3 / 5 * l ^ 2 - (Real.cosh l - 1))) := mul_nonneg hs (add_nonneg hA0 hB0)
  nlinarith [hsum]

/-- Bound on the real part of the `gaussIntegrand` exponent. -/
private lemma gaussExp_re_le (s : ℝ) (hs : 0 ≤ s) (k : ℤ) (θ l : ℝ) :
    (-(s : ℂ) / 2 * ((θ : ℂ) + (l : ℂ) * Complex.I) ^ 2
        + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I).re
      ≤ -(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2 := by
  rw [gaussExp_re]
  have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcoef : 0 ≤ 1 / 2 - 2 / Real.pi ^ 2 := by
    rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    nlinarith [hpi2]
  have hprod : 0 ≤ s * ((1 / 10) * l ^ 2 + (1 / 2 - 2 / Real.pi ^ 2) * θ ^ 2) :=
    mul_nonneg hs (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg l))
      (mul_nonneg hcoef (sq_nonneg θ)))
  nlinarith [hprod]

/-- On the line `Im z = l`, `|l| ≤ 1/2`, and for `|θ| ≤ π`, the lattice and the Gaussian
integrands differ by at most `120 s (θ⁴ + l⁴) e^{-kl + 3sl²/5} e^{-2sθ²/π²}`. -/
theorem norm_lineIntegrand_sub_gaussIntegrand_le {s : ℝ} (hs : 0 ≤ s) (k : ℤ) {θ l : ℝ}
    (hθ : |θ| ≤ Real.pi) (hl : |l| ≤ 1 / 2) :
    ‖lineIntegrand s k (θ + l * Complex.I) - gaussIntegrand s k (θ + l * Complex.I)‖
      ≤ 120 * s * (θ ^ 4 + l ^ 4) * Real.exp (-(k * l) + 3 / 5 * s * l ^ 2)
          * Real.exp (-(2 / Real.pi ^ 2) * s * θ ^ 2) := by
  unfold lineIntegrand gaussIntegrand
  set a : ℂ := -(s : ℂ) * (1 - Complex.cos ((θ : ℂ) + (l : ℂ) * Complex.I))
      + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I with ha
  set b : ℂ := -(s : ℂ) / 2 * ((θ : ℂ) + (l : ℂ) * Complex.I) ^ 2
      + (k : ℂ) * ((θ : ℂ) + (l : ℂ) * Complex.I) * Complex.I with hb
  have hdiff : a - b
      = (s : ℂ) * (Complex.cos ((θ : ℂ) + (l : ℂ) * Complex.I) - 1
          + ((θ : ℂ) + (l : ℂ) * Complex.I) ^ 2 / 2) := by
    rw [ha, hb]
    ring
  have hnorm_diff : ‖a - b‖ ≤ 120 * s * (θ ^ 4 + l ^ 4) := by
    rw [hdiff, norm_mul, Complex.norm_of_nonneg hs]
    calc s * ‖Complex.cos ((θ : ℂ) + (l : ℂ) * Complex.I) - 1
            + ((θ : ℂ) + (l : ℂ) * Complex.I) ^ 2 / 2‖
        ≤ s * (‖(θ : ℂ) + (l : ℂ) * Complex.I‖ ^ 4
            * Real.exp ‖(θ : ℂ) + (l : ℂ) * Complex.I‖) := by
          gcongr
          exact norm_cos_sub_one_add_sq_le _
      _ ≤ s * (2 * (θ ^ 4 + l ^ 4) * 55) := by
          gcongr
          · exact norm_linePoint_pow_four_le θ l
          · exact exp_norm_linePoint_le hθ hl
      _ ≤ 120 * s * (θ ^ 4 + l ^ 4) := by
          have hθ4 : 0 ≤ θ ^ 4 := by positivity
          have hl4 : 0 ≤ l ^ 4 := by positivity
          nlinarith [hs, hθ4, hl4]
  have haY : a.re ≤ -(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2 := by
    rw [ha]
    exact lineExp_re_le s hs k hθ hl
  have hbY : b.re ≤ -(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2 := by
    rw [hb]
    exact gaussExp_re_le s hs k θ l
  have hmax : max (Real.exp a.re) (Real.exp b.re)
      ≤ Real.exp (-(k * l) + 3 / 5 * s * l ^ 2)
          * Real.exp (-(2 / Real.pi ^ 2) * s * θ ^ 2) := by
    have hmax' : max (Real.exp a.re) (Real.exp b.re)
        ≤ Real.exp (-(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2) :=
      max_le (Real.exp_le_exp.mpr haY) (Real.exp_le_exp.mpr hbY)
    calc max (Real.exp a.re) (Real.exp b.re)
        ≤ Real.exp (-(k * l) + 3 / 5 * s * l ^ 2 - (2 / Real.pi ^ 2) * s * θ ^ 2) := hmax'
      _ = Real.exp (-(k * l) + 3 / 5 * s * l ^ 2)
            * Real.exp (-(2 / Real.pi ^ 2) * s * θ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
  calc ‖Complex.exp a - Complex.exp b‖
      ≤ ‖a - b‖ * max (Real.exp a.re) (Real.exp b.re) := norm_exp_sub_exp_le a b
    _ ≤ (120 * s * (θ ^ 4 + l ^ 4))
          * (Real.exp (-(k * l) + 3 / 5 * s * l ^ 2)
              * Real.exp (-(2 / Real.pi ^ 2) * s * θ ^ 2)) :=
          mul_le_mul hnorm_diff hmax (by positivity) (by positivity)
    _ = 120 * s * (θ ^ 4 + l ^ 4) * Real.exp (-(k * l) + 3 / 5 * s * l ^ 2)
          * Real.exp (-(2 / Real.pi ^ 2) * s * θ ^ 2) := by ring

/-- After the contour shift, `2π (q_s(k) - g_s(k))` is the integral over `[-π, π]` of the
difference of the two integrands minus the Gaussian integral off `[-π, π]`. -/
theorem lineKernel_sub_lineGauss_eq {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    (2 * Real.pi : ℂ) * ((lineKernel s k : ℂ) - lineGauss s k)
      = (∫ θ in (-Real.pi)..Real.pi,
            (lineIntegrand s k (θ + l * Complex.I) - gaussIntegrand s k (θ + l * Complex.I)))
        - ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I) := by
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by
    have h2pir : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h2pir
  have hQ : (2 * Real.pi : ℂ) * (lineKernel s k : ℂ)
      = ∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k (θ + l * Complex.I) := by
    rw [lineKernel_eq_integral, mul_inv_cancel_left₀ h2pi, integral_lineIntegrand_shift]
  have hG : (2 * Real.pi : ℂ) * lineGauss s k
      = ∫ θ : ℝ, gaussIntegrand s k (θ + l * Complex.I) :=
    (integral_gaussIntegrand_shift hs k l).symm
  have hsplit : (∫ θ : ℝ, gaussIntegrand s k (θ + l * Complex.I))
      = (∫ θ in Set.Icc (-Real.pi) Real.pi, gaussIntegrand s k (θ + l * Complex.I))
        + ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I) :=
    (integral_add_compl measurableSet_Icc (integrable_gaussIntegrand_shift hs k l)).symm
  have hIcc : (∫ θ in Set.Icc (-Real.pi) Real.pi, gaussIntegrand s k (θ + l * Complex.I))
      = ∫ θ in (-Real.pi)..Real.pi, gaussIntegrand s k (θ + l * Complex.I) := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hpi]
  have hsub : (∫ θ in (-Real.pi)..Real.pi,
        (lineIntegrand s k (θ + l * Complex.I) - gaussIntegrand s k (θ + l * Complex.I)))
      = (∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k (θ + l * Complex.I))
        - ∫ θ in (-Real.pi)..Real.pi, gaussIntegrand s k (θ + l * Complex.I) := by
    apply intervalIntegral.integral_sub
    · exact ((differentiable_lineIntegrand s k).continuous.comp
        (by fun_prop : Continuous fun θ : ℝ =>
          (θ : ℂ) + (l : ℂ) * Complex.I)).intervalIntegrable _ _
    · exact ((by unfold gaussIntegrand; fun_prop : Continuous fun θ : ℝ =>
        gaussIntegrand s k (θ + l * Complex.I))).intervalIntegrable _ _
  have hBC : (∫ θ in (-Real.pi)..Real.pi, gaussIntegrand s k (θ + l * Complex.I))
        + ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)
      = (2 * Real.pi : ℂ) * lineGauss s k := by
    rw [← hIcc, ← hsplit, ← hG]
  have key : (∫ θ in (-Real.pi)..Real.pi,
          (lineIntegrand s k (θ + l * Complex.I) - gaussIntegrand s k (θ + l * Complex.I)))
        - ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)
      = (2 * Real.pi : ℂ) * (lineKernel s k : ℂ)
        - (2 * Real.pi : ℂ) * lineGauss s k := by
    rw [hsub, ← hQ, ← hBC]
    ring
  rw [key, mul_sub]

/-- The norm of the shifted Gaussian integrand factors as a constant
`exp (-(k*l) + s*l²/2)` times the real Gaussian `exp (-(s/2)*θ²)`. -/
private lemma norm_gaussIntegrand_shift_expand (s : ℝ) (k : ℤ) (l θ : ℝ) :
    ‖gaussIntegrand s k (θ + l * Complex.I)‖
      = Real.exp (-(k * l) + s * l ^ 2 / 2) * Real.exp (-(s / 2) * θ ^ 2) := by
  rw [norm_gaussIntegrand_shift]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Outside `[-π, π]` the square of `θ` is at least `π²`. -/
private lemma compl_Icc_pi_sq_le (θ : ℝ) (hθ : θ ∈ (Set.Icc (-Real.pi) Real.pi)ᶜ) :
    Real.pi ^ 2 ≤ θ ^ 2 := by
  have hθ' : θ < -Real.pi ∨ Real.pi < θ := by
    rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    exact hθ
  have hpi_abs : Real.pi ≤ |θ| := by
    rcases hθ' with h | h
    · rw [abs_of_neg (by linarith [Real.pi_pos])]
      linarith
    · rw [abs_of_pos (by linarith [Real.pi_pos])]
      linarith
  rw [sq_le_sq, abs_of_nonneg Real.pi_pos.le]
  exact hpi_abs

/-- The Gaussian integral prefactor `√(π/(s/4))` rewrites as `2 √π s^(-1/2)`. -/
private lemma sqrt_pi_over_quarter (s : ℝ) (hs : 0 < s) :
    Real.sqrt (Real.pi / (s / 4)) = 2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2) := by
  have h4 : Real.pi / (s / 4) = 4 * (Real.pi / s) := by
    field_simp
  rw [h4, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (Real.pi / s)]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsqrt4, Real.sqrt_div Real.pi_pos.le s, Real.sqrt_eq_rpow s, div_eq_mul_inv,
    ← Real.rpow_neg hs.le (1 / 2 : ℝ)]
  ring_nf

/-- The Gaussian tail factor `exp (-(s*π²/4))` is bounded by `1/(1+2s)`. -/
private lemma exp_neg_quarter_le_inv (s : ℝ) (hs : 0 < s) :
    Real.exp (-(s * Real.pi ^ 2 / 4)) ≤ 1 / (1 + 2 * s) := by
  have hpi2 : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (-(s * Real.pi ^ 2 / 4)) ≤ Real.exp (-(2 * s)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hpi2, hs]
  have h3 : (1 + 2 * s : ℝ) ≤ Real.exp (2 * s) := by
    have := Real.add_one_le_exp (2 * s)
    linarith
  have h4 : 0 < 1 + 2 * s := by positivity
  calc
    Real.exp (-(s * Real.pi ^ 2 / 4)) ≤ Real.exp (-(2 * s)) := hexp
    _ = (Real.exp (2 * s))⁻¹ := Real.exp_neg (2 * s)
    _ ≤ (1 + 2 * s)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) h4).mpr h3
    _ = 1 / (1 + 2 * s) := by rw [one_div]

/-- The elementary numeric bound closing the Gaussian tail estimate. -/
private lemma sqrt_pi_rpow_le (s : ℝ) (hs : 0 < s) :
    2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2) / (1 + 2 * s)
      ≤ 2 * s ^ (-(3 : ℝ) / 2) := by
  have hpi_le : Real.sqrt Real.pi ≤ 2 := by
    have h : Real.pi ≤ 4 := by nlinarith [Real.pi_lt_d2]
    calc
      Real.sqrt Real.pi ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h
      _ = 2 := by norm_num
  have hden : 0 < 1 + 2 * s := by positivity
  have hleft : 2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2) / (1 + 2 * s)
      = 2 * s ^ (-(1 : ℝ) / 2) * (Real.sqrt Real.pi / (1 + 2 * s)) := by ring_nf
  have hright : 2 * s ^ (-(3 : ℝ) / 2) = 2 * s ^ (-(1 : ℝ) / 2) * s ^ (-1 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hs]
    norm_num
  rw [hleft, hright]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff₀ hden, Real.rpow_neg_one, inv_mul_eq_div, le_div_iff₀ hs]
  nlinarith [hpi_le, hs]

/-- The Gaussian integral off `[-π, π]` along `Im z = l` is at most
`2 e^{-kl + sl²/2} s^{-3/2}`. -/
theorem norm_integral_compl_gaussIntegrand_le {s : ℝ} (hs : 0 < s) (k : ℤ) (l : ℝ) :
    ‖∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)‖
      ≤ Real.exp (-(k * l) + s * l ^ 2 / 2) * (2 * s ^ (-(3 : ℝ) / 2)) := by
  set E : ℝ := Real.exp (-(k * l) + s * l ^ 2 / 2) with hEdef
  have hEpos : 0 < E := by rw [hEdef]; positivity
  have hSmeas : MeasurableSet ((Set.Icc (-Real.pi) Real.pi)ᶜ : Set ℝ) :=
    measurableSet_Icc.compl
  have hInt1 : Integrable fun θ : ℝ => Real.exp (-(s / 2) * θ ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hInt4 : Integrable fun θ : ℝ => Real.exp (-(s / 4) * θ ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hstep1 :
      ‖∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)‖
      ≤ ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, E * Real.exp (-(s / 2) * θ ^ 2) := by
    calc
      ‖∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)‖
          ≤ ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ,
              ‖gaussIntegrand s k (θ + l * Complex.I)‖ := by
            simpa only using
              (norm_integral_le_integral_norm
                (μ := volume.restrict (Set.Icc (-Real.pi) Real.pi)ᶜ)
                (fun θ : ℝ => gaussIntegrand s k (θ + l * Complex.I)))
      _ = ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, E * Real.exp (-(s / 2) * θ ^ 2) := by
            rw [hEdef]
            apply setIntegral_congr_fun hSmeas
            intro θ _
            exact norm_gaussIntegrand_shift_expand s k l θ
  have hstep2 : ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, E * Real.exp (-(s / 2) * θ ^ 2)
      ≤ E * Real.exp (-(s * Real.pi ^ 2 / 4))
          * ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, Real.exp (-(s / 4) * θ ^ 2) := by
    calc
      ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, E * Real.exp (-(s / 2) * θ ^ 2)
          ≤ ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ,
              E * (Real.exp (-(s * Real.pi ^ 2 / 4)) * Real.exp (-(s / 4) * θ ^ 2)) := by
            exact setIntegral_mono_on (hInt1.const_mul E).integrableOn
              ((hInt4.const_mul (Real.exp (-(s * Real.pi ^ 2 / 4)))).const_mul E).integrableOn
              hSmeas (fun θ hθ => by
                apply mul_le_mul_of_nonneg_left _ hEpos.le
                rw [← Real.exp_add]
                apply Real.exp_le_exp.mpr
                nlinarith [compl_Icc_pi_sq_le θ hθ])
      _ = E * Real.exp (-(s * Real.pi ^ 2 / 4))
            * ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, Real.exp (-(s / 4) * θ ^ 2) := by
            rw [integral_const_mul]
            rw [integral_const_mul]
            ring
  have hstep3 : ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, Real.exp (-(s / 4) * θ ^ 2)
      ≤ Real.sqrt (Real.pi / (s / 4)) := by
    calc
      ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, Real.exp (-(s / 4) * θ ^ 2)
          ≤ ∫ θ, Real.exp (-(s / 4) * θ ^ 2) := by
            exact setIntegral_le_integral hInt4
              (Filter.Eventually.of_forall fun θ => Real.exp_nonneg _)
      _ = Real.sqrt (Real.pi / (s / 4)) := integral_gaussian (s / 4)
  have hnum : Real.exp (-(s * Real.pi ^ 2 / 4)) * Real.sqrt (Real.pi / (s / 4))
      ≤ 2 * s ^ (-(3 : ℝ) / 2) := by
    rw [sqrt_pi_over_quarter s hs]
    calc
      Real.exp (-(s * Real.pi ^ 2 / 4)) * (2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2))
          ≤ (1 / (1 + 2 * s)) * (2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2)) := by
            apply mul_le_mul_of_nonneg_right (exp_neg_quarter_le_inv s hs)
            positivity
      _ = 2 * Real.sqrt Real.pi * s ^ (-(1 : ℝ) / 2) / (1 + 2 * s) := by ring
      _ ≤ 2 * s ^ (-(3 : ℝ) / 2) := sqrt_pi_rpow_le s hs
  calc
    ‖∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, gaussIntegrand s k (θ + l * Complex.I)‖
        ≤ ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, E * Real.exp (-(s / 2) * θ ^ 2) := hstep1
    _ ≤ E * Real.exp (-(s * Real.pi ^ 2 / 4))
          * ∫ θ in (Set.Icc (-Real.pi) Real.pi)ᶜ, Real.exp (-(s / 4) * θ ^ 2) := hstep2
    _ ≤ E * Real.exp (-(s * Real.pi ^ 2 / 4)) * Real.sqrt (Real.pi / (s / 4)) := by
          apply mul_le_mul_of_nonneg_left hstep3
          positivity
    _ = E * (Real.exp (-(s * Real.pi ^ 2 / 4)) * Real.sqrt (Real.pi / (s / 4))) := by ring
    _ ≤ E * (2 * s ^ (-(3 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left hnum
          positivity
    _ = Real.exp (-(k * l) + s * l ^ 2 / 2) * (2 * s ^ (-(3 : ℝ) / 2)) := by rw [hEdef]

/-- A Gaussian integral over the symmetric interval `[-π, π]` is bounded by the
full Gaussian integral over `ℝ`. -/
private lemma interval_integral_exp_neg_mul_sq_le {b : ℝ} (hb : 0 < b) :
    ∫ θ in (-Real.pi)..Real.pi, Real.exp (-b * θ ^ 2) ≤ Real.sqrt (Real.pi / b) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  calc ∫ θ in Set.Ioc (-Real.pi) Real.pi, Real.exp (-b * θ ^ 2)
      ≤ ∫ θ : ℝ, Real.exp (-b * θ ^ 2) :=
        setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
          (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)
    _ = Real.sqrt (Real.pi / b) := integral_gaussian b

/-- The quartic Gaussian moment on `[-π, π]`: `∫ θ⁴ e^{-aθ²} ≤ 8 a^{-2} √(2π/a)`. -/
theorem integral_quartic_gauss_le {a : ℝ} (ha : 0 < a) :
    ∫ θ in (-Real.pi)..Real.pi, θ ^ 4 * Real.exp (-a * θ ^ 2)
      ≤ 8 / a ^ 2 * Real.sqrt (2 * Real.pi / a) := by
  have hpt : ∀ θ : ℝ, θ ^ 4 * Real.exp (-a * θ ^ 2)
      ≤ 8 / a ^ 2 * Real.exp (-(a / 2) * θ ^ 2) := by
    intro θ
    have hu : 0 ≤ a * θ ^ 2 / 2 := by positivity
    have hquad := Real.quadratic_le_exp_of_nonneg hu
    have hu2 : (a * θ ^ 2 / 2) ^ 2 ≤ 2 * Real.exp (a * θ ^ 2 / 2) := by
      nlinarith [hquad, hu, Real.exp_pos (a * θ ^ 2 / 2)]
    have hfac : Real.exp (-a * θ ^ 2)
        = Real.exp (-(a / 2) * θ ^ 2) * Real.exp (-(a * θ ^ 2 / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfac, Real.exp_neg]
    have hth4 : θ ^ 4 = 4 / a ^ 2 * (a * θ ^ 2 / 2) ^ 2 := by
      field_simp
      ring
    rw [hth4]
    have hkey : 4 / a ^ 2 * (a * θ ^ 2 / 2) ^ 2
        * (Real.exp (a * θ ^ 2 / 2))⁻¹ ≤ 8 / a ^ 2 := by
      field_simp
      nlinarith [hu2]
    calc 4 / a ^ 2 * (a * θ ^ 2 / 2) ^ 2
          * (Real.exp (-(a / 2) * θ ^ 2) * (Real.exp (a * θ ^ 2 / 2))⁻¹)
        = (4 / a ^ 2 * (a * θ ^ 2 / 2) ^ 2 * (Real.exp (a * θ ^ 2 / 2))⁻¹)
          * Real.exp (-(a / 2) * θ ^ 2) := by ring
      _ ≤ 8 / a ^ 2 * Real.exp (-(a / 2) * θ ^ 2) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
  have hcont1 : Continuous fun θ : ℝ => θ ^ 4 * Real.exp (-a * θ ^ 2) := by fun_prop
  have hcont2 : Continuous fun θ : ℝ => 8 / a ^ 2 * Real.exp (-(a / 2) * θ ^ 2) := by
    fun_prop
  calc ∫ θ in (-Real.pi)..Real.pi, θ ^ 4 * Real.exp (-a * θ ^ 2)
      ≤ ∫ θ in (-Real.pi)..Real.pi, 8 / a ^ 2 * Real.exp (-(a / 2) * θ ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
          (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)
          (fun θ _ => hpt θ)
    _ = 8 / a ^ 2 * ∫ θ in (-Real.pi)..Real.pi, Real.exp (-(a / 2) * θ ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ 8 / a ^ 2 * Real.sqrt (Real.pi / (a / 2)) := by
        gcongr
        exact interval_integral_exp_neg_mul_sq_le (by positivity)
    _ = 8 / a ^ 2 * Real.sqrt (2 * Real.pi / a) := by
        congr 1
        congr 1
        field_simp

/-- The Gaussian integral on `[-π, π]` is at most the one on the line, `√(π/a)`. -/
theorem integral_gauss_le {a : ℝ} (ha : 0 < a) :
    ∫ θ in (-Real.pi)..Real.pi, Real.exp (-a * θ ^ 2) ≤ Real.sqrt (Real.pi / a) :=
  interval_integral_exp_neg_mul_sq_le ha

end LatticeProb.ContinuousTime
