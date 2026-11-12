/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Polar

/-!
# GM Lemma 5.8: angular estimates for the paths `L̂_x`, `L̂_y` (task P2-M2L58c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086). GM leave the paths implicit; this file is own elementary work
(see `handoff/P2-M2L58.md`): angular separation of polar points, the chord bound, the slope of
`arccos`, and the choice of a window whose angular band avoids `x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

/-- polar points whose angles differ by `κ ≤ β − α ≤ 2π − κ` are `ρ (2/π) κ` apart -/
lemma dist_polPt_angle_sep {ρ s s' α β κ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ s) (hs' : ρ ≤ s')
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ π / 2) (h1 : κ ≤ β - α) (h2 : β - α ≤ 2 * π - κ) :
    ρ * (2 / π * κ) ≤ dist (polPt s α) (polPt s' β) := by
  have hpi := Real.pi_pos
  have hk1 : 2 / π * κ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hpi]; linarith
  by_cases hA : β - α ≤ π / 2
  · have h := dist_polPt_ge_angle (s := s) hρ hs' (abs_le.2 ⟨by linarith, hA⟩)
    rw [abs_of_nonneg (by linarith)] at h
    refine le_trans ?_ h
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hρ
  by_cases hB : β - α ≤ π + π / 2
  · have h := dist_polPt_ge_of_cos_nonpos (s := s) (s' := s') (α := α) (β := β) hs
      (hρ.trans hs') (Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) hB)
    exact le_trans (mul_le_of_le_one_right hρ hk1) h
  · have e := polPt_add_int_mul_two_pi s' β (-1)
    push_cast at e
    rw [← e]
    have h := dist_polPt_ge_angle (s := s) (α := α) (β := β + -1 * (2 * π)) hρ hs'
      (abs_le.2 ⟨by linarith, by linarith⟩)
    rw [abs_of_nonpos (by linarith)] at h
    refine le_trans ?_ h
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hρ

/-- chord bound: `|s e^{iα} − s e^{iβ}| ≤ s |β − α|` -/
lemma dist_polPt_le (s α β : ℝ) (hs : 0 ≤ s) :
    dist (polPt s α) (polPt s β) ≤ s * |β - α| := by
  rw [dist_polPt]
  have e : (s : ℂ) - s * Complex.exp ((β - α : ℝ) * Complex.I) =
      -(s : ℂ) * (Complex.exp (Complex.I * (β - α : ℝ)) - 1) := by ring_nf
  rw [e, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hs]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := β - α)
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_left this hs

/-- `arccos` has slope at most `−1` -/
lemma arccos_sub_ge {x y : ℝ} (hx : -1 ≤ x) (hy : y ≤ 1) (hxy : x ≤ y) :
    y - x ≤ arccos x - arccos y := by
  have h := Real.abs_cos_sub_cos_le (arccos x) (arccos y)
  rw [Real.cos_arccos hx (by linarith), Real.cos_arccos (by linarith) hy,
    abs_of_nonneg (by linarith [Real.arccos_le_arccos hxy] : (0:ℝ) ≤ arccos x - arccos y),
    abs_of_nonpos (by linarith)] at h
  linarith

/-- **window choice**: of two windows whose angular bands `(h_l − κ, g_l + κ)` (mod `2π`) are
disjoint, at least one has `x` outside its band -/
lemma good_window {κ g0 h0 g1 h1 t : ℝ} (hκ' : κ < π / 2) (hh0 : 0 ≤ h0)
    (hh1 : 0 ≤ h1) (hg0 : g0 ≤ π) (hg1 : g1 ≤ π) (hsep : g1 + κ ≤ h0 - κ) :
    toIcoMod Real.two_pi_pos (g0 + κ) t ≤ h0 + 2 * π - κ ∨
      toIcoMod Real.two_pi_pos (g1 + κ) t ≤ h1 + 2 * π - κ := by
  by_contra hc
  push Not at hc
  obtain ⟨c0, c1⟩ := hc
  have m0 := toIcoMod_mem_Ico Real.two_pi_pos (g0 + κ) t
  have m1 := toIcoMod_mem_Ico Real.two_pi_pos (g1 + κ) t
  have key : ∀ g : ℝ, -κ < toIcoMod Real.two_pi_pos g t - 2 * π →
      toIcoMod Real.two_pi_pos g t - 2 * π < π + κ →
      toIcoMod Real.two_pi_pos g t - 2 * π = toIcoMod Real.two_pi_pos (-(π / 2)) t := by
    intro g ha hb
    rw [← toIcoMod_toIcoMod Real.two_pi_pos (-(π / 2)) g t,
      ← toIcoMod_sub Real.two_pi_pos (-(π / 2)) (toIcoMod Real.two_pi_pos g t)]
    exact ((toIcoMod_eq_self Real.two_pi_pos).2 ⟨by linarith, by linarith⟩).symm
  have e0 := key (g0 + κ) (by linarith) (by linarith [m0.2])
  have e1 := key (g1 + κ) (by linarith) (by linarith [m1.2])
  linarith [m1.2]

/-- **the angle of `y`**: if `x = 2r e^{iθx}` and `|x − y| ≥ δr > 2rκ`, the representative of
`arg y` in `[θx − 2π + κ, θx + κ)` lies in `[θx − 2π + κ, θx − κ]` -/
lemma angle_y {r δ κ θx : ℝ} {x y : ℂ} (hr : 0 < r) (hx : x = polPt (2 * r) θx)
    (hy : ‖y‖ = 2 * r) (hxy : δ * r ≤ ‖x - y‖) (hκ : 2 * r * κ < δ * r) :
    let θy := toIcoMod Real.two_pi_pos (θx - 2 * π + κ) (Complex.arg y)
    θx - 2 * π + κ ≤ θy ∧ θy ≤ θx - κ ∧ y = polPt (2 * r) θy := by
  intro θy
  have m := toIcoMod_mem_Ico Real.two_pi_pos (θx - 2 * π + κ) (Complex.arg y)
  have hyp : y = polPt (2 * r) θy := by
    have := eq_polPt_toIcoMod y (θx - 2 * π + κ); rwa [hy] at this
  refine ⟨m.1, ?_, hyp⟩
  by_contra hc
  push Not at hc
  have h := dist_polPt_le (2 * r) θx θy (by linarith)
  rw [← hx, ← hyp, dist_eq_norm] at h
  have hlt : |θy - θx| < κ := abs_lt.2 ⟨by linarith, by linarith [m.2]⟩
  have : 2 * r * |θy - θx| ≤ 2 * r * κ := mul_le_mul_of_nonneg_left hlt.le (by linarith)
  linarith

end LQGMetric.GM
