/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53H3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim5

/-!
# DZZ Lemma 5.3, the `d_i` comparison, part 3: the scale bookkeeping (P2-DZZ53H)

The scales of `l53h_di_chain` (S5L53H2) as functions of `L = log δ⁻¹`, `δ = e^{−L}`:
`λ = L^{0.6}`, `δ₁ = δ e^{−2L^{0.8}}`, `δ_a = δ₁ e^{−λ}/(α/9)`, `δ_b = δ e^{λ}/α`
(`α = ‖a‖ ∈ (0,1]`). `l53h_ev`: for large `L`, `p32Up δ₁ ≤ δ`, `δ_a < δ_b`, the scales are below
given thresholds, the five exceptional probabilities add up to at most `e^{−L^{1/4}}`, and
`log 4 + log F + L^{0.95} ≤ L^{0.96}` with `F = cor39Fac δ_b δ_a`
(errors: `log 4` from the ball cover, `log F ≤ 18 L^{0.9}` from Corollary 3.9 between `δ_a` and
`δ_b`, `L^{0.95}` from (eq-concentration-2)). Own elementary bookkeeping (as DZZ l. 2380–2385,
which only says "with high probability").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma l53h_exp_rpow (t c : ℝ) : Real.exp t ^ c = Real.exp (t * c) := (Real.exp_mul t c).symm

lemma l53h_log_inv_exp (t : ℝ) : Real.log (Real.exp t)⁻¹ = -t := by
  rw [Real.log_inv, Real.log_exp]

/-- **The scale bookkeeping of the `d_i` comparison.** -/
theorem l53h_ev {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {cB c₃ C₁ C₂ δB δ₃ δc : ℝ} (hcB : 0 < cB)
    (hc₃ : 0 < c₃) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hδB : 0 < δB) (hδ₃ : 0 < δ₃) (hδc : 0 < δc) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ))) < δB ∧
      p32Up (Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ)))) ≤ Real.exp (-L) ∧
      Real.exp (-L) * Real.exp (L ^ (0.6 : ℝ)) / α < δ₃ ∧
      Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ))) * Real.exp (-(L ^ (0.6 : ℝ))) / (α / 9) <
        Real.exp (-L) * Real.exp (L ^ (0.6 : ℝ)) / α ∧
      Real.exp (-L) < δc ∧
      (Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ)))) ^ cB +
          C₁ * Real.exp (-(L ^ (0.6 : ℝ)) ^ 2 / C₁) +
          3 * (Real.exp (-L) * Real.exp (L ^ (0.6 : ℝ)) / α) ^ c₃ +
          C₂ * Real.exp (-(L ^ (0.6 : ℝ)) ^ 2 / C₂) +
          Real.exp (-(Real.log (Real.exp (-L))⁻¹ ^ (0.7 : ℝ))) ≤
        Real.exp (-L ^ (1 / 4 : ℝ)) ∧
      Real.log 4 + Real.log (cor39Fac (Real.exp (-L) * Real.exp (L ^ (0.6 : ℝ)) / α)
          (Real.exp (-L) * Real.exp (-(2 * L ^ (0.8 : ℝ))) * Real.exp (-(L ^ (0.6 : ℝ))) /
            (α / 9))) + L ^ (0.95 : ℝ) ≤ L ^ (0.96 : ℝ) := by
  have hlα : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1
  filter_upwards [wsim_ev_basic hα hα1 0,
    l53_ev_mul_rpow_le 4 (by norm_num : (0.8 : ℝ) < 1),
    l53_ev_mul_rpow_le (Real.log 9) (p := 0) (by norm_num : (0 : ℝ) < 0.8),
    eventually_gt_atTop (-Real.log δB), eventually_gt_atTop (-2 * Real.log δ₃),
    eventually_gt_atTop (-Real.log δc),
    wsim_ev_exp_le hcB (by norm_num : (0.7 : ℝ) < 1) 1 one_pos,
    wsim_ev_exp_le (by positivity : 0 < 1 / C₁) (by norm_num : (0.7 : ℝ) < 1.2) C₁ hC₁,
    wsim_ev_exp_le (by positivity : 0 < c₃ / 2) (by norm_num : (0.7 : ℝ) < 1) 3 (by norm_num),
    wsim_ev_exp_le (by positivity : 0 < 1 / C₂) (by norm_num : (0.7 : ℝ) < 1.2) C₂ hC₂,
    l53_ev_mul_rpow_le (Real.log 5) (p := 0) (by norm_num : (0 : ℝ) < 1 / 4),
    l53_ev_mul_rpow_le 2 (by norm_num : (1 / 4 : ℝ) < 0.7),
    l53_ev_mul_rpow_le 21 (by norm_num : (0.9 : ℝ) < 0.95),
    l53_ev_mul_rpow_le 2 (by norm_num : (0.95 : ℝ) < 0.96)]
    with L hb h8 h9 hB h3 hc e1 e2 e3 e4 f1 f2 g1 g2
  obtain ⟨hL1, -, hlam0, hlamL, hL1a, -, -⟩ := hb
  simp only [Real.rpow_zero, mul_one] at h9 f1
  rw [Real.rpow_one] at h8
  set lam := L ^ (0.6 : ℝ) with hlam
  set M := L ^ (0.8 : ℝ) with hM
  have hM0 : 0 < M := Real.rpow_pos_of_pos (by linarith) _
  have hlamM : lam ≤ M := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hM9 : M ≤ L ^ (0.9 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h09 : 1 ≤ L ^ (0.9 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  -- the scales as exponentials
  have eδ₁ : Real.exp (-L) * Real.exp (-(2 * M)) = Real.exp (-(L + 2 * M)) := by
    rw [← Real.exp_add]; ring_nf
  have eδb : Real.exp (-L) * Real.exp lam / α = Real.exp (-(L - lam + Real.log α)) := by
    rw [← Real.exp_add, show -(L - lam + Real.log α) = (-L + lam) - Real.log α by ring,
      Real.exp_sub, Real.exp_log hα]
  have eδa : Real.exp (-L) * Real.exp (-(2 * M)) * Real.exp (-lam) / (α / 9) =
      Real.exp (-(L + 2 * M + lam + Real.log α - Real.log 9)) := by
    rw [← Real.exp_add, ← Real.exp_add,
      show -(L + 2 * M + lam + Real.log α - Real.log 9) =
        (-L + -(2 * M) + -lam) - (Real.log α - Real.log 9) by ring,
      Real.exp_sub, Real.exp_sub, Real.exp_log hα, Real.exp_log (by norm_num)]
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eδ₁]
    calc Real.exp (-(L + 2 * M)) < Real.exp (Real.log δB) := Real.exp_lt_exp.2 (by linarith)
      _ = δB := Real.exp_log hδB
  · rw [eδ₁]
    unfold p32Up
    rw [l53h_log_inv_exp, neg_neg, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := wsim_rpow_le_two_mul (q := 0.8) (x := L + 2 * M) (L := L) (by positivity)
      (by linarith) (by norm_num) (by norm_num)
    linarith
  · rw [eδb]
    calc Real.exp (-(L - lam + Real.log α)) < Real.exp (Real.log δ₃) :=
          Real.exp_lt_exp.2 (by linarith)
      _ = δ₃ := Real.exp_log hδ₃
  · rw [eδa, eδb]
    exact Real.exp_lt_exp.2 (by linarith)
  · calc Real.exp (-L) < Real.exp (Real.log δc) := Real.exp_lt_exp.2 (by linarith)
      _ = δc := Real.exp_log hδc
  · rw [eδ₁, eδb, l53h_exp_rpow, l53h_exp_rpow, l53h_log_inv_exp, neg_neg]
    have k1 : Real.exp (-(L + 2 * M) * cB) ≤ Real.exp (-(L ^ (0.7 : ℝ))) := by
      rw [one_mul, Real.rpow_one] at e1
      refine le_trans (Real.exp_le_exp.2 ?_) e1
      nlinarith
    have k2 : C₁ * Real.exp (-lam ^ 2 / C₁) ≤ Real.exp (-(L ^ (0.7 : ℝ))) := by
      rw [hlam, wsim_lam_sq (by linarith)]
      convert e2 using 3; ring
    have k3 : 3 * Real.exp (-(L - lam + Real.log α) * c₃) ≤ Real.exp (-(L ^ (0.7 : ℝ))) := by
      rw [Real.rpow_one] at e3
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)) e3
      nlinarith
    have k4 : C₂ * Real.exp (-lam ^ 2 / C₂) ≤ Real.exp (-(L ^ (0.7 : ℝ))) := by
      rw [hlam, wsim_lam_sq (by linarith)]
      convert e4 using 3; ring
    have k5 : 5 * Real.exp (-(L ^ (0.7 : ℝ))) ≤ Real.exp (-L ^ (1 / 4 : ℝ)) := by
      rw [show (5 : ℝ) = Real.exp (Real.log 5) by rw [Real.exp_log (by norm_num)],
        ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    linarith
  · rw [wsim_log_cor39Fac (by positivity) (by positivity), eδa, eδb, l53h_log_inv_exp,
      l53h_log_inv_exp, neg_neg, neg_neg]
    have hL2 : L + 2 * M + lam + Real.log α - Real.log 9 ≤ 2 * L := by linarith
    have hL20 : 0 ≤ L + 2 * M + lam + Real.log α - Real.log 9 := by linarith
    have a1 := wsim_rpow_le_two_mul (q := 0.9) (L := L) (by linarith : 0 ≤ L - lam + Real.log α)
      (by linarith) (by norm_num) (by norm_num)
    have a2 := wsim_rpow_le_two_mul (q := 0.8) (L := L) (by linarith : 0 ≤ L - lam + Real.log α)
      (by linarith) (by norm_num) (by norm_num)
    have a3 := wsim_rpow_le_two_mul (q := 0.9) hL20 hL2 (by norm_num) (by norm_num)
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    rw [← hM] at a2
    linarith

end DZZ
end LQGMetric
