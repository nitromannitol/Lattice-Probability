/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TwoScaleAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Lemma 3.1, auxiliary file 1: pointwise bounds for the Gaussian kernel

For `t > 0` let `kt t x = exp(-|x|²/(4t²))` (the kernel of `gaussPair`) and
`et t x = exp(-|x|²/(16t²))` (a wider comparison Gaussian).  We prove the first- and
second-order difference bounds

* `|kt x - kt (x+e)| ≤ 2 (|e|/t) et x` for `|e| ≤ t`;
* `|kt x - kt (x+e) - kt (x+f) + kt (x+e+f)| ≤ 4 (|e||f|/t²) et x` for `|e|, |f| ≤ t`;

and combine them into the four-point bound `kt_four_point`:
for `|e| ≤ u`, `|f| ≤ v`,
`|kt x - kt (x+e) - kt (x+f) + kt (x+e+f)| ≤ 4 min(1, uv/t²) (et x + et (x+e) + et (x+f) + et (x+e+f))`.
-/

noncomputable section

open Real Set

namespace LQGDimension.TwoScale

/-- Unit-scale Gaussian kernel `exp(-|x|²/4)`. -/
def k1 (x : ℂ) : ℝ := Real.exp (-‖x‖ ^ 2 / 4)

/-- Unit-scale comparison Gaussian `exp(-|x|²/16)`. -/
def e1 (x : ℂ) : ℝ := Real.exp (-‖x‖ ^ 2 / 16)

/-- The kernel of `gaussPair` at scale `t`: `exp(-|x|²/(4t²))`. -/
def kt (t : ℝ) (x : ℂ) : ℝ := Real.exp (-‖x‖ ^ 2 / (4 * t ^ 2))

/-- Comparison Gaussian at scale `t`: `exp(-|x|²/(16t²))`. -/
def et (t : ℝ) (x : ℂ) : ℝ := Real.exp (-‖x‖ ^ 2 / (16 * t ^ 2))

lemma k1_pos (x : ℂ) : 0 < k1 x := Real.exp_pos _
lemma e1_pos (x : ℂ) : 0 < e1 x := Real.exp_pos _
lemma kt_pos (t : ℝ) (x : ℂ) : 0 < kt t x := Real.exp_pos _
lemma et_pos (t : ℝ) (x : ℂ) : 0 < et t x := Real.exp_pos _

lemma kt_le_et (t : ℝ) (x : ℂ) : kt t x ≤ et t x := by
  unfold kt et
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ t ^ 2 := sq_nonneg _
  rcases eq_or_lt_of_le h2 with h | h
  · rw [← h]; simp
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg h1 h.le]

/-! ### Elementary one-variable inequalities -/

lemma exp_sq_split (r : ℝ) : Real.exp (-r ^ 2 / 4) * Real.exp (r ^ 2 / 8) =
    Real.exp (-r ^ 2 / 8) := by
  rw [← Real.exp_add]; congr 1; ring

lemma half_mul_exp_le (r : ℝ) : (1 / 2) * r * Real.exp (-r ^ 2 / 4) ≤ Real.exp (-r ^ 2 / 8) := by
  rw [← exp_sq_split r]
  have hp := Real.exp_pos (-r ^ 2 / 4)
  have h1 := Real.add_one_le_exp (r ^ 2 / 8)
  have h2 : (1 / 2) * r ≤ Real.exp (r ^ 2 / 8) := by nlinarith [sq_nonneg (r - 2)]
  calc (1 / 2) * r * Real.exp (-r ^ 2 / 4) = Real.exp (-r ^ 2 / 4) * ((1 / 2) * r) := by ring
    _ ≤ Real.exp (-r ^ 2 / 4) * Real.exp (r ^ 2 / 8) := mul_le_mul_of_nonneg_left h2 hp.le

lemma quad_mul_exp_le (r : ℝ) :
    (1 / 2 + r ^ 2 / 4) * Real.exp (-r ^ 2 / 4) ≤ 2 * Real.exp (-r ^ 2 / 8) := by
  rw [← exp_sq_split r]
  have hp := Real.exp_pos (-r ^ 2 / 4)
  have h1 := Real.add_one_le_exp (r ^ 2 / 8)
  have h2 : (1 / 2 + r ^ 2 / 4) ≤ 2 * Real.exp (r ^ 2 / 8) := by nlinarith [sq_nonneg r]
  calc (1 / 2 + r ^ 2 / 4) * Real.exp (-r ^ 2 / 4)
      = Real.exp (-r ^ 2 / 4) * (1 / 2 + r ^ 2 / 4) := by ring
    _ ≤ Real.exp (-r ^ 2 / 4) * (2 * Real.exp (r ^ 2 / 8)) := mul_le_mul_of_nonneg_left h2 hp.le
    _ = 2 * (Real.exp (-r ^ 2 / 4) * Real.exp (r ^ 2 / 8)) := by ring

lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 2) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Shifting the centre by at most `2` costs a factor `2` when passing from `exp(-|z|²/8)` to
`exp(-|x|²/16)`. -/
lemma exp_shift_le (z x : ℂ) (h : ‖z - x‖ ≤ 2) : Real.exp (-‖z‖ ^ 2 / 8) ≤ 2 * e1 x := by
  have hx : ‖x‖ ≤ ‖z‖ + 2 := by
    have := norm_sub_norm_le x z
    rw [norm_sub_rev] at this
    linarith
  have hz := norm_nonneg z
  have hxx := norm_nonneg x
  have hsq : ‖x‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 8 := by nlinarith [sq_nonneg (‖z‖ - 2)]
  have hle : -‖z‖ ^ 2 / 8 ≤ 1 / 2 + -‖x‖ ^ 2 / 16 := by linarith
  calc Real.exp (-‖z‖ ^ 2 / 8) ≤ Real.exp (1 / 2 + -‖x‖ ^ 2 / 16) := Real.exp_le_exp.2 hle
    _ = Real.exp (1 / 2) * e1 x := by rw [Real.exp_add]; rfl
    _ ≤ 2 * e1 x := by
        have := e1_pos x
        nlinarith [exp_half_lt_two]

/-! ### Derivatives along lines -/

lemma hasDerivAt_line (y e : ℂ) (l : ℝ) : HasDerivAt (fun m : ℝ => y + m • e) e l := by
  simpa using ((hasDerivAt_id l).smul_const e).const_add y

/-- `d/dm k1(y + m e) = -(1/2) ⟪y + m e, e⟫ k1(y + m e)`. -/
lemma hasDerivAt_k1_line (y e : ℂ) (l : ℝ) :
    HasDerivAt (fun m : ℝ => k1 (y + m • e))
      (-(1 / 2) * inner ℝ (y + l • e) e * k1 (y + l • e)) l := by
  have h3 := (((hasDerivAt_line y e l).norm_sq).neg.div_const 4).exp
  refine h3.congr_deriv ?_
  simp only [Pi.neg_apply, k1]
  ring

/-- Derivative of the directional derivative `g(y + m f)`, `g(z) = -(1/2)⟪z, e⟫ k1 z`. -/
lemma hasDerivAt_g_line (y e f : ℂ) (m : ℝ) :
    HasDerivAt (fun m : ℝ => -(1 / 2) * inner ℝ (y + m • f) e * k1 (y + m • f))
      (-(1 / 2) * inner ℝ f e * k1 (y + m • f) +
        -(1 / 2) * inner ℝ (y + m • f) e *
          (-(1 / 2) * inner ℝ (y + m • f) f * k1 (y + m • f))) m := by
  have hi : HasDerivAt (fun m : ℝ => inner ℝ (y + m • f) e) (inner ℝ f e) m := by
    have := (hasDerivAt_line y f m).inner ℝ (hasDerivAt_const m e)
    simpa using this
  exact (hi.const_mul (-(1 / 2 : ℝ))).mul (hasDerivAt_k1_line y f m)

/-! ### First- and second-order differences at unit scale -/

lemma k1_sub_le (x e : ℂ) (he : ‖e‖ ≤ 1) : |k1 x - k1 (x + e)| ≤ 2 * ‖e‖ * e1 x := by
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun m : ℝ => k1 (x + m • e))
    (f' := fun l => -(1 / 2) * inner ℝ (x + l • e) e * k1 (x + l • e)) (C := 2 * ‖e‖ * e1 x)
    (fun l _ => (hasDerivAt_k1_line x e l).hasDerivWithinAt) ?_
  · simp only [one_smul, zero_smul, add_zero, Real.norm_eq_abs] at hmv
    rw [abs_sub_comm]; exact hmv
  · intro l hl
    set z := x + l • e with hz
    have hzx : ‖z - x‖ ≤ 2 := by
      rw [hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
      nlinarith [hl.2, norm_nonneg e]
    have hin := abs_real_inner_le_norm z e
    have hk := k1_pos z
    have hne := norm_nonneg e
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hk]
    calc |-(1 / 2 : ℝ)| * |inner ℝ z e| * k1 z ≤ (1 / 2) * (‖z‖ * ‖e‖) * k1 z := by
          rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
          gcongr
      _ = ‖e‖ * ((1 / 2) * ‖z‖ * Real.exp (-‖z‖ ^ 2 / 4)) := by unfold k1; ring
      _ ≤ ‖e‖ * Real.exp (-‖z‖ ^ 2 / 8) := mul_le_mul_of_nonneg_left (half_mul_exp_le _) hne
      _ ≤ ‖e‖ * (2 * e1 x) := mul_le_mul_of_nonneg_left (exp_shift_le z x hzx) hne
      _ = 2 * ‖e‖ * e1 x := by ring

/-- Bound on the derivative of `g` along `f`. -/
lemma g_deriv_bound (e f z : ℂ) :
    |-(1 / 2) * inner ℝ f e * k1 z + -(1 / 2) * inner ℝ z e * (-(1 / 2) * inner ℝ z f * k1 z)| ≤
      ‖e‖ * ‖f‖ * (2 * Real.exp (-‖z‖ ^ 2 / 8)) := by
  have h1 := abs_real_inner_le_norm f e
  have h2 := abs_real_inner_le_norm z e
  have h3 := abs_real_inner_le_norm z f
  have hk := k1_pos z
  have hne := norm_nonneg e
  have hnf := norm_nonneg f
  have hnz := norm_nonneg z
  have hq := quad_mul_exp_le ‖z‖
  have heq : -(1 / 2) * inner ℝ f e * k1 z + -(1 / 2) * inner ℝ z e * (-(1 / 2) * inner ℝ z f * k1 z)
      = k1 z * (-(1 / 2) * inner ℝ f e + (1 / 4) * (inner ℝ z e * inner ℝ z f)) := by ring
  rw [heq, abs_mul, abs_of_pos hk]
  have hA : |-(1 / 2) * inner ℝ f e + (1 / 4) * (inner ℝ z e * inner ℝ z f)| ≤
      ‖e‖ * ‖f‖ * (1 / 2 + ‖z‖ ^ 2 / 4) := by
    calc _ ≤ |-(1 / 2) * inner ℝ f e| + |(1 / 4) * (inner ℝ z e * inner ℝ z f)| := abs_add_le _ _
      _ = (1 / 2) * |inner ℝ f e| + (1 / 4) * (|inner ℝ z e| * |inner ℝ z f|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg]; norm_num
      _ ≤ (1 / 2) * (‖f‖ * ‖e‖) + (1 / 4) * ((‖z‖ * ‖e‖) * (‖z‖ * ‖f‖)) := by
          gcongr
      _ = ‖e‖ * ‖f‖ * (1 / 2 + ‖z‖ ^ 2 / 4) := by ring
  calc k1 z * |-(1 / 2) * inner ℝ f e + (1 / 4) * (inner ℝ z e * inner ℝ z f)|
      ≤ k1 z * (‖e‖ * ‖f‖ * (1 / 2 + ‖z‖ ^ 2 / 4)) := mul_le_mul_of_nonneg_left hA hk.le
    _ = ‖e‖ * ‖f‖ * ((1 / 2 + ‖z‖ ^ 2 / 4) * Real.exp (-‖z‖ ^ 2 / 4)) := by unfold k1; ring
    _ ≤ ‖e‖ * ‖f‖ * (2 * Real.exp (-‖z‖ ^ 2 / 8)) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hne hnf)

lemma k1_mixed_le (x e f : ℂ) (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1) :
    |k1 x - k1 (x + e) - k1 (x + f) + k1 (x + e + f)| ≤ 4 * ‖e‖ * ‖f‖ * e1 x := by
  have hne := norm_nonneg e
  have hnf := norm_nonneg f
  -- ψ(l) = k1(x + l e) - k1((x + f) + l e)
  have hψ : ∀ l : ℝ, HasDerivAt (fun m : ℝ => k1 (x + m • e) - k1 ((x + f) + m • e))
      (-(1 / 2) * inner ℝ (x + l • e) e * k1 (x + l • e) -
        -(1 / 2) * inner ℝ ((x + f) + l • e) e * k1 ((x + f) + l • e)) l := fun l =>
    (hasDerivAt_k1_line x e l).sub (hasDerivAt_k1_line (x + f) e l)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun m : ℝ => k1 (x + m • e) - k1 ((x + f) + m • e)) (C := 4 * ‖e‖ * ‖f‖ * e1 x)
    (fun l _ => (hψ l).hasDerivWithinAt) ?_
  · simp only [one_smul, zero_smul, add_zero, Real.norm_eq_abs] at hmv
    have heq : k1 x - k1 (x + e) - k1 (x + f) + k1 (x + e + f) =
        -(k1 (x + e) - k1 (x + f + e) - (k1 x - k1 (x + f))) := by
      rw [add_right_comm x f e]; ring
    rw [heq, abs_neg]; exact hmv
  · intro l hl
    set y := x + l • e with hy
    have hyx : ‖y - x‖ ≤ 1 := by
      rw [hy, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
      nlinarith [hl.2]
    have hyf : (x + f) + l • e = y + f := by rw [hy]; abel
    rw [hyf]
    -- χ(m) = g(y + m f)
    have hmv2 := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun m : ℝ => -(1 / 2) * inner ℝ (y + m • f) e * k1 (y + m • f))
      (C := 4 * ‖e‖ * ‖f‖ * e1 x)
      (fun m _ => (hasDerivAt_g_line y e f m).hasDerivWithinAt) ?_
    · simp only [one_smul, zero_smul, add_zero] at hmv2
      rw [norm_sub_rev]; exact hmv2
    · intro m hm
      set z := y + m • f with hz
      have hzx : ‖z - x‖ ≤ 2 := by
        have h1 : ‖z - y‖ ≤ 1 := by
          rw [hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm.1]
          nlinarith [hm.2]
        calc ‖z - x‖ = ‖(z - y) + (y - x)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
          _ ≤ 2 := by linarith
      rw [Real.norm_eq_abs]
      calc _ ≤ ‖e‖ * ‖f‖ * (2 * Real.exp (-‖z‖ ^ 2 / 8)) := g_deriv_bound e f z
        _ ≤ ‖e‖ * ‖f‖ * (2 * (2 * e1 x)) := by
            gcongr; exact exp_shift_le z x hzx
        _ = 4 * ‖e‖ * ‖f‖ * e1 x := by ring

/-! ### Scaling -/

lemma norm_div_ofReal (x : ℂ) {t : ℝ} (ht : 0 < t) : ‖x / (t : ℂ)‖ = ‖x‖ / t := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

lemma kt_eq_k1 {t : ℝ} (ht : 0 < t) (x : ℂ) : kt t x = k1 (x / (t : ℂ)) := by
  unfold kt k1
  rw [norm_div_ofReal x ht]
  congr 1
  field_simp

lemma et_eq_e1 {t : ℝ} (ht : 0 < t) (x : ℂ) : et t x = e1 (x / (t : ℂ)) := by
  unfold et e1
  rw [norm_div_ofReal x ht]
  congr 1
  field_simp

lemma kt_sub_le {t : ℝ} (ht : 0 < t) (x e : ℂ) (he : ‖e‖ ≤ t) :
    |kt t x - kt t (x + e)| ≤ 2 * (‖e‖ / t) * et t x := by
  rw [kt_eq_k1 ht, kt_eq_k1 ht, et_eq_e1 ht, add_div]
  have h := k1_sub_le (x / (t : ℂ)) (e / (t : ℂ))
    (by rw [norm_div_ofReal e ht, div_le_one ht]; exact he)
  rwa [norm_div_ofReal e ht] at h

lemma kt_mixed_le {t : ℝ} (ht : 0 < t) (x e f : ℂ) (he : ‖e‖ ≤ t) (hf : ‖f‖ ≤ t) :
    |kt t x - kt t (x + e) - kt t (x + f) + kt t (x + e + f)| ≤
      4 * (‖e‖ / t) * (‖f‖ / t) * et t x := by
  rw [kt_eq_k1 ht, kt_eq_k1 ht, kt_eq_k1 ht, kt_eq_k1 ht, et_eq_e1 ht]
  simp only [add_div]
  have h := k1_mixed_le (x / (t : ℂ)) (e / (t : ℂ)) (f / (t : ℂ))
    (by rw [norm_div_ofReal e ht, div_le_one ht]; exact he)
    (by rw [norm_div_ofReal f ht, div_le_one ht]; exact hf)
  rwa [norm_div_ofReal e ht, norm_div_ofReal f ht] at h

/-! ### The four-point bound -/

/-- **Four-point bound for the Gaussian kernel.**  If `|e| ≤ u` and `|f| ≤ v`, then the mixed
difference of `kt t` is at most `4 min(1, uv/t²)` times the sum of the four comparison
Gaussians. -/
theorem kt_four_point {t u v : ℝ} (ht : 0 < t) (hu : 0 ≤ u) (hv : 0 ≤ v) (x e f : ℂ)
    (he : ‖e‖ ≤ u) (hf : ‖f‖ ≤ v) :
    |kt t x - kt t (x + e) - kt t (x + f) + kt t (x + e + f)| ≤
      4 * min 1 (u * v / t ^ 2) *
        (et t x + et t (x + e) + et t (x + f) + et t (x + e + f)) := by
  have p1 := et_pos t x
  have p2 := et_pos t (x + e)
  have p3 := et_pos t (x + f)
  have p4 := et_pos t (x + e + f)
  have q1 := kt_le_et t x
  have q2 := kt_le_et t (x + e)
  have q3 := kt_le_et t (x + f)
  have q4 := kt_le_et t (x + e + f)
  have r1 := kt_pos t x
  have r2 := kt_pos t (x + e)
  have r3 := kt_pos t (x + f)
  have r4 := kt_pos t (x + e + f)
  have ht2 : 0 < t ^ 2 := by positivity
  set S := et t x + et t (x + e) + et t (x + f) + et t (x + e + f) with hS
  have hS0 : 0 ≤ S := by positivity
  have hne := norm_nonneg e
  have hnf := norm_nonneg f
  rcases le_or_gt u t with hut | hut <;> rcases le_or_gt v t with hvt | hvt
  · -- both small: second-order bound
    have h := kt_mixed_le ht x e f (he.trans hut) (hf.trans hvt)
    have hm : u * v / t ^ 2 ≤ 1 := by
      rw [div_le_one ht2]; nlinarith
    rw [min_eq_right hm]
    calc _ ≤ 4 * (‖e‖ / t) * (‖f‖ / t) * et t x := h
      _ ≤ 4 * (u / t) * (v / t) * et t x := by gcongr
      _ = 4 * (u * v / t ^ 2) * et t x := by field_simp
      _ ≤ 4 * (u * v / t ^ 2) * S := by
          gcongr; linarith
  · -- `u ≤ t < v`: difference in `e`
    have h1 := kt_sub_le ht x e (he.trans hut)
    have h2 := kt_sub_le ht (x + f) e (he.trans hut)
    rw [add_right_comm x f e] at h2
    have hm : u / t ≤ min 1 (u * v / t ^ 2) := by
      refine le_min ((div_le_one ht).2 hut) ?_
      rw [div_le_div_iff₀ ht ht2]
      nlinarith [mul_nonneg (mul_nonneg hu ht.le) (sub_nonneg.2 hvt.le)]
    have hmn : 0 ≤ u / t := by positivity
    calc _ = |(kt t x - kt t (x + e)) - (kt t (x + f) - kt t (x + e + f))| := by ring_nf
      _ ≤ |kt t x - kt t (x + e)| + |kt t (x + f) - kt t (x + e + f)| := abs_sub _ _
      _ ≤ 2 * (‖e‖ / t) * et t x + 2 * (‖e‖ / t) * et t (x + f) := add_le_add h1 h2
      _ ≤ 2 * (u / t) * et t x + 2 * (u / t) * et t (x + f) := by gcongr
      _ ≤ 2 * (u / t) * S := by
          have : 0 ≤ 2 * (u / t) * (et t (x + e) + et t (x + e + f)) := by positivity
          rw [hS]; linarith
      _ ≤ 4 * min 1 (u * v / t ^ 2) * S := by
          have := mul_le_mul_of_nonneg_right hm hS0
          have := mul_nonneg hmn hS0
          linarith
  · -- `v ≤ t < u`: difference in `f`
    have h1 := kt_sub_le ht x f (hf.trans hvt)
    have h2 := kt_sub_le ht (x + e) f (hf.trans hvt)
    have hm : v / t ≤ min 1 (u * v / t ^ 2) := by
      refine le_min ((div_le_one ht).2 hvt) ?_
      rw [div_le_div_iff₀ ht ht2]
      nlinarith [mul_nonneg (mul_nonneg hv ht.le) (sub_nonneg.2 hut.le)]
    have hmn : 0 ≤ v / t := by positivity
    calc _ = |(kt t x - kt t (x + f)) - (kt t (x + e) - kt t (x + e + f))| := by ring_nf
      _ ≤ |kt t x - kt t (x + f)| + |kt t (x + e) - kt t (x + e + f)| := abs_sub _ _
      _ ≤ 2 * (‖f‖ / t) * et t x + 2 * (‖f‖ / t) * et t (x + e) := add_le_add h1 h2
      _ ≤ 2 * (v / t) * et t x + 2 * (v / t) * et t (x + e) := by gcongr
      _ ≤ 2 * (v / t) * S := by
          have : 0 ≤ 2 * (v / t) * (et t (x + f) + et t (x + e + f)) := by positivity
          rw [hS]; linarith
      _ ≤ 4 * min 1 (u * v / t ^ 2) * S := by
          have := mul_le_mul_of_nonneg_right hm hS0
          have := mul_nonneg hmn hS0
          linarith
  · -- both large: trivial bound
    have hm : 1 ≤ u * v / t ^ 2 := by
      rw [le_div_iff₀ ht2]; nlinarith
    rw [min_eq_left hm]
    calc _ ≤ |kt t x| + |kt t (x + e)| + |kt t (x + f)| + |kt t (x + e + f)| := by
          have := abs_sub (kt t x) (kt t (x + e))
          have := abs_sub (kt t x - kt t (x + e)) (kt t (x + f))
          have := abs_add_le (kt t x - kt t (x + e) - kt t (x + f)) (kt t (x + e + f))
          linarith
      _ ≤ S := by
          rw [abs_of_pos r1, abs_of_pos r2, abs_of_pos r3, abs_of_pos r4]; linarith
      _ ≤ 4 * 1 * S := by linarith

end LQGDimension.TwoScale
