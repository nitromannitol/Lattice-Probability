/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Polar at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# GM Lemma 5.8: circular arcs and radial segments (task P2-M2L58b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086): the paths `L_k`, `L̂_x`, `L̂_y` are left implicit in GM; this
module provides the polar pieces of our explicit choice (own construction): arcs
`arcSet ρ θ₁ θ₂ = {ρ e^{iθ} : θ ∈ [θ₁, θ₂]}` and radial segments
`radSet θ ρ₁ ρ₂ = {s e^{iθ} : s ∈ [ρ₁, ρ₂]}` (compact, connected), with the two distance bounds used
to separate them: `|‖p‖ − ‖q‖| ≤ |p − q|`, and for `s, s' ≥ ρ > 0` and angles `α, β`,
`|s e^{iα} − s' e^{iβ}| ≥ ρ · (2/π)|α − β|` if `|α − β| ≤ π/2` (Jordan's inequality,
`Real.mul_le_sin`) and `≥ ρ` if `π/2 ≤ |α − β| ≤ 3π/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Complex
open scoped Real

namespace LQGMetric.GM

/-- the polar point `s e^{iθ}` -/
def polPt (s θ : ℝ) : ℂ := (s : ℂ) * exp (θ * I)

lemma continuous_polPt_angle (s : ℝ) : Continuous (fun θ : ℝ => polPt s θ) :=
  continuous_const.mul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

lemma continuous_polPt_radius (θ : ℝ) : Continuous (fun s : ℝ => polPt s θ) :=
  Complex.continuous_ofReal.mul continuous_const

lemma norm_polPt {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) : ‖polPt s θ‖ = s := by
  rw [polPt, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hs]

/-- the arc `{ρ e^{iθ} : θ ∈ [θ₁, θ₂]}` -/
def arcSet (ρ θ₁ θ₂ : ℝ) : Set ℂ := (fun θ : ℝ => polPt ρ θ) '' Icc θ₁ θ₂

/-- the radial segment `{s e^{iθ} : s ∈ [ρ₁, ρ₂]}` -/
def radSet (θ ρ₁ ρ₂ : ℝ) : Set ℂ := (fun s : ℝ => polPt s θ) '' Icc ρ₁ ρ₂

lemma isCompact_arcSet (ρ θ₁ θ₂ : ℝ) : IsCompact (arcSet ρ θ₁ θ₂) :=
  isCompact_Icc.image (continuous_polPt_angle ρ)

lemma isCompact_radSet (θ ρ₁ ρ₂ : ℝ) : IsCompact (radSet θ ρ₁ ρ₂) :=
  isCompact_Icc.image (continuous_polPt_radius θ)

lemma isConnected_arcSet (ρ : ℝ) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) : IsConnected (arcSet ρ θ₁ θ₂) :=
  (isConnected_Icc h).image _ (continuous_polPt_angle ρ).continuousOn

lemma isConnected_radSet (θ : ℝ) {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) : IsConnected (radSet θ ρ₁ ρ₂) :=
  (isConnected_Icc h).image _ (continuous_polPt_radius θ).continuousOn

/-- points at different distances from `0` are apart -/
lemma norm_sub_le_dist (p q : ℂ) : |‖p‖ - ‖q‖| ≤ dist p q := by
  rw [dist_eq_norm]; exact abs_norm_sub_norm_le p q

/-- `|s e^{iα} − s' e^{iβ}| = |s − s' e^{i(β − α)}|` -/
lemma dist_polPt (s s' α β : ℝ) :
    dist (polPt s α) (polPt s' β) = ‖(s : ℂ) - s' * exp ((β - α : ℝ) * I)‖ := by
  rw [dist_eq_norm, polPt, polPt]
  have e : (s : ℂ) * exp (α * I) - s' * exp (β * I) =
      exp (α * I) * ((s : ℂ) - s' * exp ((β - α : ℝ) * I)) := by
    rw [mul_sub, ← mul_assoc, mul_comm (exp (α * I)) (s' : ℂ), mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [e, norm_mul, norm_exp_ofReal_mul_I, one_mul]

/-- **angular separation, small angles** (Jordan's inequality) -/
lemma dist_polPt_ge_angle {ρ s s' α β : ℝ} (hρ : 0 ≤ ρ) (hs' : ρ ≤ s')
    (hαβ : |β - α| ≤ π / 2) : ρ * (2 / π * |β - α|) ≤ dist (polPt s α) (polPt s' β) := by
  rw [dist_polPt]
  set φ := β - α
  have him : ((s : ℂ) - s' * exp (φ * I)).im = -(s' * Real.sin φ) := by
    rw [Complex.sub_im, Complex.ofReal_im, Complex.im_ofReal_mul, exp_ofReal_mul_I_im]; ring
  have h1 : |s' * Real.sin φ| ≤ ‖(s : ℂ) - s' * exp (φ * I)‖ := by
    have := Complex.abs_im_le_norm ((s : ℂ) - s' * exp (φ * I))
    rwa [him, abs_neg] at this
  have hsin : 2 / π * |φ| ≤ |Real.sin φ| := by
    rcases le_total 0 φ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by
        linarith [abs_le.1 hαβ, Real.pi_pos]))]
      exact Real.mul_le_sin h (by linarith [abs_le.1 hαβ])
    · rw [abs_of_nonpos h, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by
        linarith [abs_le.1 hαβ, Real.pi_pos]))]
      have := Real.mul_le_sin (x := -φ) (by linarith) (by linarith [abs_le.1 hαβ])
      rw [Real.sin_neg] at this
      linarith
  have hs0 : 0 ≤ s' := hρ.trans hs'
  rw [abs_mul, abs_of_nonneg hs0] at h1
  have hp : 0 ≤ 2 / π * |φ| := by positivity
  calc ρ * (2 / π * |φ|) ≤ s' * |Real.sin φ| := mul_le_mul hs' hsin hp hs0
    _ ≤ _ := h1

/-- **angular separation, large angles** -/
lemma dist_polPt_ge_of_cos_nonpos {ρ s s' α β : ℝ} (hs : ρ ≤ s) (hs' : 0 ≤ s')
    (hcos : Real.cos (β - α) ≤ 0) : ρ ≤ dist (polPt s α) (polPt s' β) := by
  rw [dist_polPt]
  have hre : ((s : ℂ) - s' * exp ((β - α : ℝ) * I)).re = s - s' * Real.cos (β - α) := by
    rw [Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, exp_ofReal_mul_I_re]
  have := Complex.re_le_norm ((s : ℂ) - s' * exp ((β - α : ℝ) * I))
  rw [hre] at this
  nlinarith

/-- `polPt` is `2π`-periodic in the angle -/
lemma polPt_add_int_mul_two_pi (s θ : ℝ) (k : ℤ) : polPt s (θ + k * (2 * π)) = polPt s θ := by
  unfold polPt
  push_cast
  congr 1
  exact (Complex.exp_mul_I_periodic.int_mul k) (θ : ℂ)

/-- every point is `|x| e^{iθ}` for every representative `θ` of `arg x` modulo `2π` -/
lemma eq_polPt_toIcoMod (x : ℂ) (a : ℝ) :
    x = polPt ‖x‖ (toIcoMod Real.two_pi_pos a (arg x)) := by
  have h := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos a (arg x)
  rw [zsmul_eq_mul] at h
  conv_lhs => rw [← norm_mul_exp_arg_mul_I x]
  rw [← polPt_add_int_mul_two_pi ‖x‖ _ (toIcoDiv Real.two_pi_pos a (arg x)), h]
  rfl

lemma polPt_re (s θ : ℝ) : (polPt s θ).re = s * Real.cos θ := by
  rw [polPt, Complex.re_ofReal_mul, exp_ofReal_mul_I_re]

lemma polPt_im (s θ : ℝ) : (polPt s θ).im = s * Real.sin θ := by
  rw [polPt, Complex.im_ofReal_mul, exp_ofReal_mul_I_im]

/-- a radial ray leaving the circle `ρ₁` at real part `b` stays `(|b − a|)/2` away from every
point of real part `a` inside that circle -/
lemma dist_rad_vert {ρ₁ a b γ s : ℝ} (hρ : 0 < ρ₁) (hcos : ρ₁ * Real.cos γ = b) (hs : ρ₁ ≤ s)
    {q : ℂ} (hq : q.re = a) (hqn : ‖q‖ ≤ ρ₁) : |b - a| / 2 ≤ dist (polPt s γ) q := by
  have hre := polPt_re s γ
  have hre' : (polPt s γ).re = s / ρ₁ * b := by
    rw [hre, ← hcos]; field_simp
  have h1 : |(polPt s γ).re - a| ≤ dist (polPt s γ) q := by
    rw [← hq, dist_eq_norm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : s - ρ₁ ≤ dist (polPt s γ) q := by
    have := norm_sub_le_dist (polPt s γ) q
    rw [norm_polPt (hρ.le.trans hs)] at this
    linarith [le_abs_self (s - ‖q‖)]
  have hk : 1 ≤ s / ρ₁ := by rw [le_div_iff₀ hρ]; linarith
  have hb : |b| ≤ ρ₁ := by
    rw [← hcos, abs_mul, abs_of_pos hρ]
    exact mul_le_of_le_one_right hρ.le (Real.abs_cos_le_one γ)
  -- either the real parts are far apart, or the radius has grown
  by_contra hlt
  push Not at hlt
  have e1 : |s / ρ₁ * b - a| < |b - a| / 2 := by rw [← hre']; linarith
  have e2 : s - ρ₁ < |b - a| / 2 := by linarith
  have e3 : (s / ρ₁ - 1) * |b| ≤ s - ρ₁ := by
    have : (s / ρ₁ - 1) * ρ₁ = s - ρ₁ := by field_simp
    nlinarith
  have e4 : |b - a| ≤ |s / ρ₁ * b - a| + (s / ρ₁ - 1) * |b| := by
    have h := abs_add_le (s / ρ₁ * b - a) (-((s / ρ₁ - 1) * b))
    rw [abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s / ρ₁ - 1)] at h
    have : s / ρ₁ * b - a + -((s / ρ₁ - 1) * b) = b - a := by ring
    rwa [this] at h
  linarith

/-- the vertical line `Re = t` meets the circle `ρ` (upper half) at angle `arccos (t/ρ)` -/
lemma polPt_arccos {ρ t : ℝ} (hρ : 0 < ρ) (ht : |t| ≤ ρ) :
    polPt ρ (Real.arccos (t / ρ)) = ⟨t, Real.sqrt (ρ ^ 2 - t ^ 2)⟩ := by
  have h1 : -1 ≤ t / ρ := by rw [le_div_iff₀ hρ]; linarith [(abs_le.1 ht).1]
  have h2 : t / ρ ≤ 1 := by rw [div_le_iff₀ hρ]; linarith [(abs_le.1 ht).2]
  apply Complex.ext
  · rw [polPt_re, Real.cos_arccos h1 h2]; field_simp
  · rw [polPt_im, Real.sin_arccos]
    have e : ρ ^ 2 - t ^ 2 = ρ ^ 2 * (1 - (t / ρ) ^ 2) := by field_simp
    rw [e, Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le]

end LQGMetric.GM
