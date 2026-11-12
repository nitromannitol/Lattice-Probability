/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61H2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61H1

/-!
# D117 P-61G (5): `DZZL61GlueK` from the scale-uniform coupling (P2-DZZ125)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 2562–2568, 2605 (Fig. glue), with the scaling
argument of (eq-z-open) (l. 2474, 2501–2503) in the form of decision D125 (`DZZSimCoupleScale`,
factor `‖a‖`): at scale `d = 2^{−m}/40 ∈ [δ^κ, 2δ^κ]`, the 40 tilde crossings of the ring around
`v ∈ L_δ` are each `≤ N = ⌊δ^{−(χ−ι)}/40⌋` with probability `→ 1` (`prob_not_pairsOK_le` with
`λ = (m+1)^{3/4}`, and DZZ Lemma 5.3 + Proposition 3.17 at the fixed pair, `dzz_lem53_upper_whp`
at `ι/2`), and then the deterministic gluing `ring_glue_lgd` gives
`min_{∂} D(v, ·) ≤ min_{L × ∂} D + 40 N`. Plan: handoff P2-DZZ61G §6 (statement adapted:
`hκ1 : κ < 1` (D125), `DZZProp317In` and `ξ ≤ 1/80` for `dzz_lem53_upper_whp`, see report).

The asymptotics (`tendsto_exp_rpow34_sub`, `tendsto_scaleTail`) are own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- `A (n+1)^{3/4} − B n → −∞`, exponentiated (own elementary proof). -/
lemma tendsto_exp_rpow34_sub (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (fun n : ℕ => Real.exp (A * ((n : ℝ) + 1) ^ (3 / 4 : ℝ) - B * n)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have hlin : Tendsto (fun n : ℕ => B - B / 2 * ((n : ℝ) + 1)) atTop atBot := by
    have h1 : Tendsto (fun n : ℕ => B / 2 * ((n : ℝ) + 1)) atTop atTop :=
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
        (by positivity)
    exact tendsto_atBot_add_const_left _ B (tendsto_neg_atTop_atBot.comp h1)
  refine tendsto_atBot_mono' _ ?_ hlin
  set R := (2 * |A| / B) ^ (4 : ℝ)
  filter_upwards [(tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).eventually_ge_atTop
    R] with n hn
  set x : ℝ := (n : ℝ) + 1
  have hx0 : 0 < x := by positivity
  have hsplit : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have h14 : 2 * |A| / B ≤ x ^ (1 / 4 : ℝ) := by
    have : (R) ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hn (by norm_num)
    rwa [← Real.rpow_mul (by positivity), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  have h34 : 0 ≤ x ^ (3 / 4 : ℝ) := by positivity
  have hA : A * x ^ (3 / 4 : ℝ) ≤ B / 2 * x := by
    calc A * x ^ (3 / 4 : ℝ) ≤ |A| * x ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) h34
      _ = B / 2 * (2 * |A| / B) * x ^ (3 / 4 : ℝ) := by field_simp
      _ ≤ B / 2 * x ^ (1 / 4 : ℝ) * x ^ (3 / 4 : ℝ) := by gcongr
      _ = B / 2 * x := by rw [mul_assoc, mul_comm (x ^ (1 / 4 : ℝ)), hsplit]
  simp only [x] at hA ⊢
  linarith

/-- `C e^{−λ²/(C(m+1))} → 0` for `λ = (m+1)^{3/4}` (own elementary proof). -/
lemma tendsto_scaleTail {C : ℝ} (hC : 0 < C) :
    Tendsto (fun n : ℕ => C * Real.exp (-(((n : ℝ) + 1) ^ (3 / 4 : ℝ)) ^ 2 / (C * ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  have e : ∀ n : ℕ, -(((n : ℝ) + 1) ^ (3 / 4 : ℝ)) ^ 2 / (C * ((n : ℝ) + 1)) =
      -(((n : ℝ) + 1) ^ (1 / 2 : ℝ) / C) := by
    intro n
    have hx0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [sq, ← Real.rpow_add hx0, show (3 / 4 : ℝ) + 3 / 4 = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx0, Real.rpow_one]
    field_simp
  simp_rw [e]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / 2 : ℝ) / C) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).atTop_div_const hC
  have h2 := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)).const_mul C
  rw [mul_zero] at h2
  exact h2

lemma compl_tildeBox_nonempty' {u v : ℂ} (huv : u ≠ v) : (tildeBox u v)ᶜ.Nonempty := by
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv))
  refine ⟨(u + v) / 2 + 2 * (v - u), fun h => ?_⟩
  have h1 := h.1
  have he : ((u + v) / 2 + 2 * (v - u) - (u + v) / 2) * starRingEnd ℂ (v - u) =
      ((2 * ‖v - u‖ ^ 2 : ℝ) : ℂ) := by
    rw [add_sub_cancel_left, mul_assoc, Complex.mul_conj']
    push_cast; ring
  rw [he, Complex.ofReal_re, abs_of_pos (by positivity)] at h1
  nlinarith

lemma mem_kXi_of_ball_subset' {K : Set ℂ} {z : ℂ} {r : ℝ} (hne : (Kᶜ).Nonempty)
    (hb : Metric.ball z r ⊆ K) : z ∈ kXi K r := by
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  by_contra hlt
  push Not at hlt
  exact hy (hb (Metric.mem_ball'.mpr hlt))

/-- `u ∈ (𝕍̃_{u,v})^ξ` for `2ξ ≤ |u − v|` (copied from S5Walls1, P2-DZZADAPT). -/
lemma mem_kXi_tildeBox_left' {u v : ℂ} (huv : u ≠ v) {ξ : ℝ} (hξ : 2 * ξ ≤ dist u v) :
    u ∈ kXi (tildeBox u v) ξ := by
  have hb : Metric.ball u (‖v - u‖ / 2) ⊆ tildeBox u v := by
    refine Subset.trans (fun z hz => ?_) (ball_mid_subset_tildeBox u v)
    rw [Metric.mem_ball] at hz ⊢
    have hum : dist u ((u + v) / 2) = ‖v - u‖ / 2 := by
      rw [dist_eq_norm, show u - (u + v) / 2 = -((v - u) / 2) by ring, norm_neg, norm_div]
      simp
    linarith [dist_triangle z u ((u + v) / 2)]
  have h := mem_kXi_of_ball_subset' (compl_tildeBox_nonempty' huv) hb
  have hd : dist u v = ‖v - u‖ := by rw [dist_eq_norm, norm_sub_rev]
  exact le_trans (show ξ ≤ ‖v - u‖ / 2 by linarith) h

lemma mem_kXi_tildeBox_right' {u v : ℂ} (huv : u ≠ v) {ξ : ℝ} (hξ : 2 * ξ ≤ dist u v) :
    v ∈ kXi (tildeBox u v) ξ := by
  have hb : Metric.ball v (‖v - u‖ / 2) ⊆ tildeBox u v := by
    refine Subset.trans (fun z hz => ?_) (ball_mid_subset_tildeBox u v)
    rw [Metric.mem_ball] at hz ⊢
    have hvm : dist v ((u + v) / 2) = ‖v - u‖ / 2 := by
      rw [dist_eq_norm, show v - (u + v) / 2 = (v - u) / 2 by ring, norm_div]
      simp
    linarith [dist_triangle z v ((u + v) / 2)]
  have h := mem_kXi_of_ball_subset' (compl_tildeBox_nonempty' huv) hb
  have hd : dist u v = ‖v - u‖ := by rw [dist_eq_norm, norm_sub_rev]
  exact le_trans (show ξ ≤ ‖v - u‖ / 2 by linarith) h

/-- (copied from S5Adapt, P2-DZZADAPT) -/
lemma edge_of_mem_frontier_sqBox' {u b : ℂ} {l : ℝ} (hl : 0 < l)
    (hb : b ∈ frontier (sqBox u l)) : |b.re - u.re| = l / 2 ∨ |b.im - u.im| = l / 2 := by
  rw [frontier_sqBox hl] at hb
  rcases hb with ((⟨_, hb⟩ | ⟨hb, _⟩) | ⟨_, hb⟩) | ⟨hb, _⟩
  · right; rw [mem_singleton_iff.mp hb, show u.im - l / 2 - u.im = -(l / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  · left; rw [mem_singleton_iff.mp hb, show u.re - l / 2 - u.re = -(l / 2) by ring, abs_neg,
      abs_of_pos (by positivity)]
  · right; rw [mem_singleton_iff.mp hb, show u.im + l / 2 - u.im = l / 2 by ring,
      abs_of_pos (by positivity)]
  · left; rw [mem_singleton_iff.mp hb, show u.re + l / 2 - u.re = l / 2 by ring,
      abs_of_pos (by positivity)]

end DZZ
end LQGMetric
