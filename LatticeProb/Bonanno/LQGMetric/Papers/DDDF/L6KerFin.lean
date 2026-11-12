/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerFin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerInc

/-!
# DDDF Lemma 6, Step 3: increment and variance bounds for `φ_L`

DDDF (arXiv:1904.08021, `tightness.tex` l. 577–640; Dubédat–Falconet arXiv:1809.02607,
Lemmas 4.1, 4.2): uniformly in `δ > 0` and `x, x' ∈ K`,

* `l6_lKer_inc`: `‖lKer x − lKer x'‖² ≤ C|x − x'|` (the `W`-part: `φ₁`, `φ_{2,1}`, `φ_{2,3}`);
* `l6_gKer_inc`: `‖gKer x − gKer x'‖² ≤ C|x − x'|` (the `W'`-part `φ_{2,2}`);
* `l6_inc_phiL`: `E(φ_L(x) − φ_L(x'))² ≤ C|x − x'|`; `l6_var_phiL`: `Var φ_L(x) ≤ C`.

Hypotheses: those supplied by DDDF Lemma 12′ (`U` open, bounded; `F` holomorphic, injective;
`1 ≤ |F'| ≤ M`, `|F''| ≤ M₂` on `U`; `K ⊆ U` compact). DDDF also assume `U`, `V`, `K` convex
(l. 539, 545); we do not need it (deviation D-DDDF-L6-convex, see `exists_geom`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

lemma exp_le_of_kappa {s r τ t M κ : ℝ} (hκ0 : 0 < κ) (hs : κ * r ≤ s) (hr : 0 ≤ r)
    (hτ : 0 < τ) (hτM : τ ≤ M ^ 2 * t) (ht : 0 < t) (hM : 0 < M) :
    Real.exp (-s ^ 2 / τ) ≤ Real.exp (-r ^ 2 / ((M / κ) ^ 2 * t)) := by
  apply Real.exp_le_exp.2
  rw [neg_div, neg_div, neg_le_neg_iff]
  have e : r ^ 2 / ((M / κ) ^ 2 * t) = (κ * r) ^ 2 / (M ^ 2 * t) := by field_simp
  rw [e]
  calc (κ * r) ^ 2 / (M ^ 2 * t) ≤ s ^ 2 / (M ^ 2 * t) := by
        gcongr
    _ ≤ s ^ 2 / τ := div_le_div_of_nonneg_left (sq_nonneg s) hτ hτM

lemma norm_sub_sq_le_two (a b : WNSpace) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_sub_le a b
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- Large-time increment of the kernel of `φ_L` (DDDF Step 3(A)). -/
lemma sq_lKerFun_sub_le (h : ConfHyp F U) (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M ε κ : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) {x x' : ℂ} (hball : ball x ε ⊆ U) (hxx : ‖x - x'‖ < ε)
    (hκx : ∀ y ∈ U, κ * ‖x - y‖ ≤ ‖F x - F y‖) (hκx' : ∀ y ∈ U, κ * ‖x' - y‖ ≤ ‖F x' - F y‖)
    {t : ℝ} (hht : ‖x - x'‖ < t) (ht1 : t ≤ 1) (y : ℂ) :
    (lKerFun F U δ x (t, y) - lKerFun F U δ x' (t, y)) ^ 2 ≤
      40 * M ^ 4 / Real.pi ^ 2 * ‖x - x'‖ ^ 2 / t ^ 3 *
        (Real.exp (-‖x - y‖ ^ 2 / ((M / κ) ^ 2 * t)) +
          Real.exp (-‖x' - y‖ ^ 2 / ((M / κ) ^ 2 * t))) := by
  have hpi := Real.pi_pos
  set hd := ‖x - x'‖ with hhd
  have hh0 : 0 ≤ hd := norm_nonneg _
  have ht0 : 0 < t := lt_of_le_of_lt hh0 hht
  have hh2 : hd ^ 2 ≤ t := by nlinarith
  have hML : M ≤ M / κ := by rw [le_div_iff₀ hκ0]; nlinarith
  have hL1 : 1 ≤ M / κ := hM1.trans hML
  have hε : 0 < ε := lt_of_le_of_lt hh0 hxx
  have hx'b : x' ∈ ball x ε := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hxx
  have hB' : ConfHyp F (ball x ε) := confHyp_mono h isOpen_ball hball
  have hη : ‖F x - F x'‖ ≤ M * hd :=
    norm_F_sub_le hB' (convex_ball x ε) (fun z hz => hM z (hball hz)) (mem_ball_self hε) hx'b
  set Ex := Real.exp (-‖x - y‖ ^ 2 / ((M / κ) ^ 2 * t))
  set Ex' := Real.exp (-‖x' - y‖ ^ 2 / ((M / κ) ^ 2 * t))
  have hRHS : 0 ≤ 40 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') := by positivity
  -- the `â` increment
  have hA : ((Real.pi * t)⁻¹ * Real.exp (-‖x - y‖ ^ 2 / t) -
      (Real.pi * t)⁻¹ * Real.exp (-‖x' - y‖ ^ 2 / t)) ^ 2 ≤
      10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') := by
    have hMM : 1 ≤ M ^ 2 := by nlinarith
    refine (gauss_sub_sq_le ht0 le_rfl (by nlinarith) hM1 hh2
      (le_mul_of_one_le_left hh0 hM1)).trans ?_
    gcongr
    · exact exp_le_gauss hL1 ht0
    · exact exp_le_gauss hL1 ht0
  rw [lKerFun_eq hF1 hδ, lKerFun_eq hF1 hδ]
  by_cases hAm : (t, y) ∈ setA δ
  swap
  · have hB : (t, y) ∉ setB F U δ := fun hB => hAm (setB_subset_setA hF1 δ hB)
    simp only [indicator_of_notMem hB, indicator_of_notMem hAm, sub_zero]
    simpa using hRHS
  by_cases hBm : (t, y) ∈ setB F U δ
  · rw [indicator_of_mem hBm, indicator_of_mem hBm, indicator_of_mem hAm, indicator_of_mem hAm]
    obtain ⟨-, hy, htc⟩ := hBm
    simp only at hy htc
    simp only [aHat, bHat] at hA ⊢
    have hc1 : 1 ≤ ‖deriv F y‖ ^ 2 := by nlinarith [hF1 y hy]
    have hcM : ‖deriv F y‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM y hy) 2
    have hτ1 : t ≤ t * ‖deriv F y‖ ^ 2 := le_mul_of_one_le_right ht0.le hc1
    have hτ2 : t * ‖deriv F y‖ ^ 2 ≤ M ^ 2 * t := by nlinarith
    have hτ0 : 0 < t * ‖deriv F y‖ ^ 2 := ht0.trans_le hτ1
    have hBd := gauss_sub_sq_le ht0 hτ1 hτ2 hM1 hh2 (z := F y) hη
    have hBd' : ((Real.pi * t)⁻¹ * Real.exp (-‖F x - F y‖ ^ 2 / (t * ‖deriv F y‖ ^ 2)) -
        (Real.pi * t)⁻¹ * Real.exp (-‖F x' - F y‖ ^ 2 / (t * ‖deriv F y‖ ^ 2))) ^ 2 ≤
        10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') := by
      refine hBd.trans ?_
      gcongr
      · exact exp_le_of_kappa hκ0 (hκx y hy) (norm_nonneg _) hτ0 hτ2 ht0 (by linarith)
      · exact exp_le_of_kappa hκ0 (hκx' y hy) (norm_nonneg _) hτ0 hτ2 ht0 (by linarith)
    set a := (Real.pi * t)⁻¹ * Real.exp (-‖F x - F y‖ ^ 2 / (t * ‖deriv F y‖ ^ 2)) -
        (Real.pi * t)⁻¹ * Real.exp (-‖F x' - F y‖ ^ 2 / (t * ‖deriv F y‖ ^ 2))
    set b := (Real.pi * t)⁻¹ * Real.exp (-‖x - y‖ ^ 2 / t) -
      (Real.pi * t)⁻¹ * Real.exp (-‖x' - y‖ ^ 2 / t)
    calc _ = (a - b) ^ 2 := by simp only [a, b]; ring
      _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
      _ ≤ 2 * (10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex')) +
          2 * (10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex')) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ 10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') := by positivity
          have e : 40 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') =
              4 * (10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex')) := by ring
          rw [e]; linarith
  · rw [indicator_of_notMem hBm, indicator_of_notMem hBm, indicator_of_mem hAm,
      indicator_of_mem hAm]
    simp only [aHat] at hA ⊢
    have : 0 ≤ 10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') := by positivity
    calc _ = ((Real.pi * t)⁻¹ * Real.exp (-‖x - y‖ ^ 2 / t) -
          (Real.pi * t)⁻¹ * Real.exp (-‖x' - y‖ ^ 2 / t)) ^ 2 := by ring
      _ ≤ _ := hA.trans (by
          have e : 40 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex') =
              4 * (10 * M ^ 4 / Real.pi ^ 2 * hd ^ 2 / t ^ 3 * (Ex + Ex')) := by ring
          rw [e]; linarith)

/-- **DDDF Lemma 6, Step 3: increments of the `W`-kernel of `φ_L`** (`φ₁`, `φ_{2,1}`, `φ_{2,3}`). -/
theorem l6_lKer_inc (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, ∀ x' ∈ K,
      ‖lKer F U δ x - lKer F U δ x'‖ ^ 2 ≤ C * ‖x - x'‖ := by
  set M' := max M 1
  set M₂' := max M₂ 0
  have hM1 : 1 ≤ M' := le_max_right _ _
  have hM' : ∀ y ∈ U, ‖deriv F y‖ ≤ M' := fun y hy => (hM y hy).trans (le_max_left _ _)
  have hM2' : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂' := fun y hy => (hM2 y hy).trans
    (le_max_left _ _)
  obtain ⟨ε, κ, hε, hκ0, hκ1, -, hball, hκ⟩ :=
    exists_geom h hUb hF1 (le_max_right M₂ 0) hM2' hK hKU
  set L := M' / κ
  set C₀ := cBd L M₂' ε
  set C₁ := C₀ * (Real.pi * L ^ 2)
  set K₀ := 40 * M' ^ 4 / Real.pi ^ 2
  have hC₀ : 0 ≤ C₀ := cBd_nonneg _ _ _ (by positivity)
  have hC₁ : 0 ≤ C₁ := by positivity
  have hbd : ∀ δ, 0 < δ → ∀ x ∈ K, ‖lKer F U δ x‖ ^ 2 ≤ C₁ := fun δ hδ x hx =>
    norm_sq_lKer_le h hF1 hM1 hM' (le_max_right _ _) hM2' hε hκ0 hκ1 hδ (hball x hx) (hκ x hx)
  refine ⟨4 * C₁ / ε + (4 * C₀ + 2 * K₀) * (Real.pi * L ^ 2), fun δ hδ x hx x' hx' => ?_⟩
  set hd := ‖x - x'‖ with hhd
  have hh0 : 0 ≤ hd := norm_nonneg _
  have hK₀ : 0 ≤ K₀ := by positivity
  rcases hh0.eq_or_lt with h0 | hpos
  · have : x = x' := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    rw [← h0, this, sub_self, norm_zero]; norm_num
  by_cases hfar : ε ≤ hd
  · have h1 := norm_sub_sq_le_two (lKer F U δ x) (lKer F U δ x')
    have h2 : 4 * C₁ ≤ 4 * C₁ / ε * hd := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    nlinarith [hbd δ hδ x hx, hbd δ hδ x' hx', mul_nonneg (by positivity : (0 : ℝ) ≤
      (4 * C₀ + 2 * K₀) * (Real.pi * L ^ 2)) hh0]
  push Not at hfar
  have hae : ((lKer F U δ x - lKer F U δ x' : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun p => lKerFun F U δ x p - lKerFun F U δ x' p := by
    filter_upwards [Lp.coeFn_sub (lKer F U δ x) (lKer F U δ x'), coeFn_lKer h hδ x,
      coeFn_lKer h hδ x'] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hmain := lintegral_inc_le hC₀ hK₀ (by positivity : (0 : ℝ) < L ^ 2) hpos
    (sq_lKerFun_le h hF1 hM1 hM' (le_max_right _ _) hM2' hε hκ0 hκ1 hδ (hball x hx) (hκ x hx))
    (sq_lKerFun_le h hF1 hM1 hM' (le_max_right _ _) hM2' hε hκ0 hκ1 hδ (hball x' hx')
      (hκ x' hx'))
    (fun t y hht ht1 => sq_lKerFun_sub_le h hF1 hM1 hM' hκ0 hκ1 hδ (hball x hx) hfar (hκ x hx)
      (hκ x' hx') hht ht1 y)
  have := norm_sq_le_of_ae hae (fun p => le_rfl) (by positivity) hmain
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * C₁ / ε) hh0]

end DDDF
end LQGMetric
