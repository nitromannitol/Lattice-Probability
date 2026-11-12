/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214SepMob at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, node R4 (tools): the Cayley-type map `z ↦ i (q + z)/(q − z)` and paths

Tools for the crosscut separation in the proof of CONF Lemma 2.14 (Gwynne–Miller,
arXiv:1905.00381, confluence-final.tex 866–869): for `|q| = 1` the Möbius map
`l214Mob q z = i (q + z)/(q − z)` sends the unit disc onto the upper half-plane, `q ↦ ∞`,
`−q ↦ 0`, and the circle onto the real line; `Im = (1 − |z|²)/|q − z|²` and on the circle
`Re = −2 Im(ζ q̄)/|q − ζ|²`. Standard (Ahlfors, *Complex Analysis*, Ch. 3 §3.4); own elementary
computations. Also straight-segment paths `l214SegPath` and the image of a path under a map
continuous on its range (`l214PathMapOn`).
-/

namespace LQGMetric
namespace CONF

open Set Complex
open scoped ComplexConjugate

/-- The Möbius map `z ↦ i (q + z)/(q − z)`. -/
noncomputable def l214Mob (q z : ℂ) : ℂ := I * (q + z) / (q - z)

theorem l214Mob_im {q z : ℂ} (hq : ‖q‖ = 1) (hz : z ≠ q) :
    (l214Mob q z).im = (1 - ‖z‖ ^ 2) / ‖q - z‖ ^ 2 := by
  have hq' : q.re ^ 2 + q.im ^ 2 = 1 := by
    have := Complex.sq_norm q; rw [hq, Complex.normSq_apply] at this; nlinarith
  have hne : q - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hN : normSq (q - z) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [l214Mob, mul_div_assoc, Complex.mul_im, I_re, I_im, zero_mul, one_mul, zero_add,
    div_re, Complex.sq_norm, Complex.sq_norm (q - z)]
  rw [← add_div, Complex.normSq_apply z]
  congr 1
  simp only [add_re, sub_re, add_im, sub_im]
  linear_combination hq'

theorem l214Mob_re_of_ne {q ζ : ℂ} (hζ : ζ ≠ q) :
    (l214Mob q ζ).re = -2 * (ζ * conj q).im / ‖q - ζ‖ ^ 2 := by
  rw [l214Mob, mul_div_assoc, Complex.mul_re, I_re, I_im, zero_mul, one_mul, zero_sub,
    div_im, Complex.sq_norm (q - ζ)]
  rw [← sub_div, ← neg_div]
  congr 1
  simp only [add_re, sub_re, add_im, sub_im, mul_im, conj_re, conj_im]
  ring

theorem l214Mob_eq_ofReal {q ζ : ℂ} (hq : ‖q‖ = 1) (hζ : ‖ζ‖ = 1) (hζq : ζ ≠ q) :
    l214Mob q ζ = ((l214Mob q ζ).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [l214Mob_im hq hζq, hζ]; simp

theorem l214Mob_injOn {q : ℂ} (hq : q ≠ 0) {z₁ z₂ : ℂ} (h₁ : z₁ ≠ q) (h₂ : z₂ ≠ q)
    (h : l214Mob q z₁ = l214Mob q z₂) : z₁ = z₂ := by
  have e₁ : q - z₁ ≠ 0 := sub_ne_zero.2 (Ne.symm h₁)
  have e₂ : q - z₂ ≠ 0 := sub_ne_zero.2 (Ne.symm h₂)
  unfold l214Mob at h
  rw [div_eq_div_iff e₁ e₂] at h
  have : (2 * I * q) * (z₁ - z₂) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · exfalso
    simp only [mul_eq_zero, two_ne_zero, I_ne_zero, false_or] at h0
    exact hq h0
  · exact sub_eq_zero.1 h0

theorem continuousOn_l214Mob (q : ℂ) : ContinuousOn (l214Mob q) {z | z ≠ q} := by
  unfold l214Mob
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => sub_ne_zero.2 (Ne.symm hz)

theorem l214Mob_neg_smul {q : ℂ} (hq : q ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖l214Mob q (-((s : ℂ) * q))‖ = |1 - s| / (1 + s) := by
  have hden : q - -((s : ℂ) * q) = ((1 + s : ℝ) : ℂ) * q := by push_cast; ring
  have hnum : q + -((s : ℂ) * q) = ((1 - s : ℝ) : ℂ) * q := by push_cast; ring
  rw [l214Mob, hden, hnum, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < 1 + s)]
  have : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  field_simp

theorem l214Mob_norm_ge {q z : ℂ} (hq : ‖q‖ = 1) {δ : ℝ} (hδ : 0 < δ) (hz : ‖q - z‖ ≤ δ)
    (hzq : z ≠ q) : (2 - δ) / δ ≤ ‖l214Mob q z‖ := by
  have hpos : 0 < ‖q - z‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hzq))
  have hsum : 2 - ‖q - z‖ ≤ ‖q + z‖ := by
    have h := norm_sub_norm_le (2 * q) (q - z)
    have e : 2 * q - (q - z) = q + z := by ring
    rw [e, norm_mul, hq] at h; norm_num at h; linarith
  rw [l214Mob, norm_div, norm_mul, Complex.norm_I, one_mul]
  rw [div_le_div_iff₀ hδ hpos]
  nlinarith

/-- The straight path `t ↦ x + t (y − x)`. -/
noncomputable def l214SegPath (x y : ℂ) : Path x y where
  toFun t := x + ((t : ℝ) : ℂ) * (y - x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem l214SegPath_apply (x y : ℂ) (t : unitInterval) :
    l214SegPath x y t = x + ((t : ℝ) : ℂ) * (y - x) := rfl

/-- The image of a path under a map continuous on its range. -/
noncomputable def l214PathMapOn {x y : ℂ} (γ : Path x y) (f : ℂ → ℂ) (hf : ContinuousOn f (range γ)) :
    Path (f x) (f y) where
  toFun t := f (γ t)
  continuous_toFun := hf.comp_continuous γ.continuous fun t => mem_range_self t
  source' := by simp
  target' := by simp

end CONF
end LQGMetric
