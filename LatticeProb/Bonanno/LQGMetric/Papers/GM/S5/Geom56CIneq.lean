/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CIneq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CPaths

/-!
# GM Lemma 5.6: depth estimates for the corridors (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6, condition (2)
(l. 2982–2989), corridor of decision D69.

The corridor at `u` (axis `e` within `45°` of the outward normal `(u − z)/|u − z|`) runs from
`u` inward. A point `w` whose `e`-coordinate is `τ ∈ [17 s, 100 s]` behind `u` and whose
transverse offset is `|δ| ≤ 3 s` satisfies `|w − z| ≤ R − 4 s` (`R = |u − z|`, `s ≤ R/20000`):
it is at distance `≥ 4 s` inside the circle through `u` (`depth_in`). At depth `τ ≥ 48 s` it is
`25 s` inside (`depth_in'`). For the corridor at `v` (axis within `45°` of the inward normal, the
corridor running outward) `|w − z| ≥ R + 4 s` (`depth_out`), and the linear functional
`Re ((w − z) conj (v − z)) ≥ R² + 30 R s` at depth `τ ≥ 48 s` (`depth_out_lin`).
Own elementary estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM

lemma norm_mul_conj_unit {e : ℂ} (he : ‖e‖ = 1) (w : ℂ) : ‖w * (starRingEnd ℂ) e‖ = ‖w‖ := by
  rw [norm_mul, Complex.norm_conj, he, mul_one]

lemma norm_sq_re_im (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- the common algebra: `(w − z) ē = (u − z) ē − (τ + i δ)` -/
lemma depth_eq {z u c e w : ℂ} :
    (w - z) * (starRingEnd ℂ) e = (u - z) * (starRingEnd ℂ) e -
      ((u - c) * (starRingEnd ℂ) e - (w - c) * (starRingEnd ℂ) e) := by ring

lemma depth_sq {z u c e w : ℂ} (he : ‖e‖ = 1) :
    ‖w - z‖ ^ 2 = (((u - z) * (starRingEnd ℂ) e).re -
        (((u - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re)) ^ 2 +
      (((u - z) * (starRingEnd ℂ) e).im -
        (((u - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im)) ^ 2 := by
  rw [← norm_mul_conj_unit he, norm_sq_re_im, depth_eq (u := u) (c := c)]
  simp only [Complex.sub_re, Complex.sub_im]

/-- the real inequality behind `depth_in`, `depth_in'` -/
lemma depth_real {R s x y τ δ k τ₀ : ℝ} (hs : 0 < s) (hxy : x ^ 2 + y ^ 2 = R ^ 2) (hR : 0 ≤ R)
    (hx : 7 / 10 * R ≤ x) (hτ1 : τ₀ * s ≤ τ) (hτ2 : τ ≤ 100 * s) (hδ : |δ| ≤ 3 * s)
    (hk : 0 ≤ k) (hkR : k * s ≤ R) (hτ₀ : 0 ≤ τ₀)
    (hmain : 2 * k * R * s + 10009 * s ^ 2 ≤ 2 * (7 / 10 * τ₀ - 3) * R * s + k ^ 2 * s ^ 2) :
    (x - τ) ^ 2 + (y - δ) ^ 2 ≤ (R - k * s) ^ 2 := by
  have hτ0 : 0 ≤ τ := le_trans (mul_nonneg hτ₀ hs.le) hτ1
  have hy : |y| ≤ R := by
    rw [← abs_of_nonneg hR]; apply sq_le_sq.1; nlinarith
  have h1 : 7 / 10 * R * τ ≤ x * τ := mul_le_mul_of_nonneg_right hx hτ0
  have h2 : 7 / 10 * R * (τ₀ * s) ≤ 7 / 10 * R * τ := mul_le_mul_of_nonneg_left hτ1 (by positivity)
  have h3 : -(R * (3 * s)) ≤ y * δ := by
    have : |y * δ| ≤ R * (3 * s) := by
      rw [abs_mul]; exact mul_le_mul hy hδ (abs_nonneg _) hR
    linarith [neg_abs_le (y * δ)]
  have h4 : τ ^ 2 ≤ (100 * s) ^ 2 := pow_le_pow_left₀ hτ0 hτ2 2
  have h5 : δ ^ 2 ≤ (3 * s) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  nlinarith

/-- **inside the corridor at `u`, depth `≥ 17 s`**: `|w − z| ≤ R − 4 s` -/
theorem depth_in {z u c e w : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 20000 * s ≤ R) (he : ‖e‖ = 1)
    (hu : ‖u - z‖ = R) (ha : 7 / 10 * R ≤ ((u - z) * (starRingEnd ℂ) e).re)
    (hτ1 : 17 * s ≤ ((u - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re)
    (hτ2 : ((u - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re ≤ 100 * s)
    (hδ : |((u - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im| ≤ 3 * s) :
    ‖w - z‖ ≤ R - 4 * s := by
  have hxy : ((u - z) * (starRingEnd ℂ) e).re ^ 2 + ((u - z) * (starRingEnd ℂ) e).im ^ 2 = R ^ 2 := by
    rw [← norm_sq_re_im, norm_mul_conj_unit he, hu]
  have := depth_real hs hxy (by linarith) ha hτ1 hτ2 hδ (by norm_num : (0 : ℝ) ≤ 4) (by linarith)
    (by norm_num) (by nlinarith)
  rw [← depth_sq he] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 this

/-- **inside the corridor at `u`, depth `≥ 48 s`**: `|w − z| ≤ R − 25 s` -/
theorem depth_in' {z u c e w : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 20000 * s ≤ R) (he : ‖e‖ = 1)
    (hu : ‖u - z‖ = R) (ha : 7 / 10 * R ≤ ((u - z) * (starRingEnd ℂ) e).re)
    (hτ1 : 48 * s ≤ ((u - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re)
    (hτ2 : ((u - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re ≤ 100 * s)
    (hδ : |((u - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im| ≤ 3 * s) :
    ‖w - z‖ ≤ R - 25 * s := by
  have hxy : ((u - z) * (starRingEnd ℂ) e).re ^ 2 + ((u - z) * (starRingEnd ℂ) e).im ^ 2 = R ^ 2 := by
    rw [← norm_sq_re_im, norm_mul_conj_unit he, hu]
  have := depth_real hs hxy (by linarith) ha hτ1 hτ2 hδ (by norm_num : (0 : ℝ) ≤ 25) (by linarith)
    (by norm_num) (by nlinarith)
  rw [← depth_sq he] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 this

/-- **outside, along the corridor at `v`**: `|w − z| ≥ R + 4 s` -/
theorem depth_out {z v c e w : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 20000 * s ≤ R) (he : ‖e‖ = 1)
    (hv : ‖v - z‖ = R) (ha : ((v - z) * (starRingEnd ℂ) e).re ≤ -(7 / 10 * R))
    (hτ1 : 17 * s ≤ ((v - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re)
    (hδ : |((v - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im| ≤ 3 * s) :
    R + 4 * s ≤ ‖w - z‖ := by
  set x := ((v - z) * (starRingEnd ℂ) e).re
  set y := ((v - z) * (starRingEnd ℂ) e).im
  set τ := ((v - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re
  set δ := ((v - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im
  have hxy : x ^ 2 + y ^ 2 = R ^ 2 := by
    rw [← norm_sq_re_im, norm_mul_conj_unit he, hv]
  have hR0 : 0 ≤ R := by linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hy : |y| ≤ R := by
    rw [← abs_of_nonneg hR0]; apply sq_le_sq.1; nlinarith
  have h1 : x * τ ≤ -(7 / 10 * R) * τ := mul_le_mul_of_nonneg_right ha hτ0
  have h2 : 7 / 10 * R * (17 * s) ≤ 7 / 10 * R * τ := mul_le_mul_of_nonneg_left hτ1 (by positivity)
  have h3 : y * δ ≤ R * (3 * s) := by
    have : |y * δ| ≤ R * (3 * s) := by
      rw [abs_mul]; exact mul_le_mul hy hδ (abs_nonneg _) hR0
    linarith [le_abs_self (y * δ)]
  have key : (R + 4 * s) ^ 2 ≤ ‖w - z‖ ^ 2 := by
    rw [depth_sq (u := v) (c := c) he]
    nlinarith [sq_nonneg τ, sq_nonneg δ]
  exact (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).1 key

/-- **the linear functional along the corridor at `v`**, depth `≥ 48 s` -/
theorem depth_out_lin {z v c e w : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (he : ‖e‖ = 1)
    (hv : ‖v - z‖ = R) (ha : ((v - z) * (starRingEnd ℂ) e).re ≤ -(7 / 10 * R))
    (hτ1 : 48 * s ≤ ((v - c) * (starRingEnd ℂ) e).re - ((w - c) * (starRingEnd ℂ) e).re)
    (hδ : |((v - c) * (starRingEnd ℂ) e).im - ((w - c) * (starRingEnd ℂ) e).im| ≤ 3 * s) :
    R ^ 2 + 30 * R * s ≤ ((w - z) * (starRingEnd ℂ) (v - z)).re := by
  set X := (v - z) * (starRingEnd ℂ) e
  set ζ := (v - c) * (starRingEnd ℂ) e - (w - c) * (starRingEnd ℂ) e
  have hee : e * (starRingEnd ℂ) e = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, he]; norm_num
  have hv' : v - z = X * e := by
    simp only [X]; rw [mul_assoc, mul_comm ((starRingEnd ℂ) e) e, hee, mul_one]
  have hw : (w - z) * (starRingEnd ℂ) (v - z) = (X - ζ) * (starRingEnd ℂ) X := by
    rw [hv', map_mul, ← depth_eq (u := v) (c := c)]; ring
  have hX : X.re ^ 2 + X.im ^ 2 = R ^ 2 := by
    rw [← norm_sq_re_im, norm_mul_conj_unit he, hv]
  have hy : |X.im| ≤ R := by
    rw [← abs_of_nonneg hR]; apply sq_le_sq.1; nlinarith
  have hτ0 : 0 ≤ ζ.re := by simp only [ζ, Complex.sub_re]; linarith
  have h1 : X.re * ζ.re ≤ -(7 / 10 * R) * ζ.re := mul_le_mul_of_nonneg_right ha hτ0
  have h2 : 7 / 10 * R * (48 * s) ≤ 7 / 10 * R * ζ.re := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); simp only [ζ, Complex.sub_re]; linarith
  have h3 : X.im * ζ.im ≤ R * (3 * s) := by
    have : |X.im * ζ.im| ≤ R * (3 * s) := by
      rw [abs_mul]; refine mul_le_mul hy ?_ (abs_nonneg _) hR
      simpa only [ζ, Complex.sub_im] using hδ
    linarith [le_abs_self (X.im * ζ.im)]
  rw [hw]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im] at *
  nlinarith

end LQGMetric.GM
