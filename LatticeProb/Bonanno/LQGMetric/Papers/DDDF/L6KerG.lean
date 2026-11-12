/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerFin

/-!
# DDDF Lemma 6, Step 3: the `W'`-part `φ_{2,2}` and the bounds for `φ_L`

DDDF (arXiv:1904.08021, `tightness.tex` l. 626–640, "Second term": "The first two terms are
similar"): the kernel `gKer x = k_{δ,F(x)} 1_{((0,∞)×V)ᶜ}` only sees `z ∉ V`, at distance
`≥ d = d(F(K), Vᶜ)` from `F(x)`; the increment is split at `t = |x − x'|` exactly as for `φ_{2,1}`
(`lintegral_inc_le`), with `|F x − F x'| ≤ M|x − x'|` for `|x − x'| < ε`.

Consequences (DDDF Step 2, l. 577–582): `l6_inc_phiL` (`E(φ_L x − φ_L x')² ≤ C|x − x'|`) and
`l6_var_phiL` (`Var φ_L(x) ≤ C`), uniformly in `δ > 0`, `x, x' ∈ K`.
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

/-- The explicit function representing `gKer h δ x`. -/
def gKerFun (F : ℂ → ℂ) (U : Set ℂ) (δ : ℝ) (x : ℂ) (p : ℝ × ℂ) : ℝ :=
  (pushTarget F U)ᶜ.indicator (fun q => (setA δ).indicator (aHat (F x)) q) p

lemma coeFn_gKer (h : ConfHyp F U) {δ : ℝ} (hδ : 0 < δ) (x : ℂ) :
    (gKer h δ x : ℝ × ℂ → ℝ) =ᵐ[volume] gKerFun F U δ x := by
  filter_upwards [coeFn_cutL2 h.measurableSet_pushTarget.compl (phiKernelL2 δ 1 (F x)),
    coeFn_phiKernelL2 δ 1 hδ (F x)] with p h1 h2
  rw [gKer, h1, gKerFun]
  by_cases hp : p ∈ (pushTarget F U)ᶜ
  · rw [indicator_of_mem hp, indicator_of_mem hp, h2, phiKernel_eq_setA]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

lemma sq_gKerFun_le {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) {x : ℂ}
    (hx : ∀ z ∉ F '' U, d ≤ ‖F x - z‖) (p : ℝ × ℂ) :
    gKerFun F U δ x p ^ 2 ≤ gaussR (Ioc 0 1) (fun t => 1 / (Real.pi ^ 2 * d ^ 2) / t) 1 (F x) p := by
  have hn : 0 ≤ gaussR (Ioc 0 1) (fun t => 1 / (Real.pi ^ 2 * d ^ 2) / t) 1 (F x) p :=
    gaussR_nonneg (fun t ht => by have := (mem_Ioc.1 ht).1; positivity) _ _ _
  obtain ⟨t, z⟩ := p
  rw [gKerFun]
  by_cases hp : (t, z) ∈ (pushTarget F U)ᶜ
  swap
  · rw [indicator_of_notMem hp]; simpa using hn
  rw [indicator_of_mem hp]
  by_cases hA : (t, z) ∈ setA δ
  swap
  · simp only [indicator_of_notMem hA]; simpa using hn
  simp only [indicator_of_mem hA]
  obtain ⟨ht1, -⟩ := mem_prod.1 hA
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1.1
  have hz : z ∉ F '' U := fun hz => hp (mk_mem_prod (show t ∈ Ioi 0 from ht0) hz)
  rw [gaussR_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1.2⟩), aHat]
  have := aHat_sq_le_far (M := 1) le_rfl ht0 hd (hx z hz)
  rwa [one_pow] at this

/-- **DDDF Lemma 6, Step 3: increments of the `W'`-kernel of `φ_L`** (`φ_{2,2}`). -/
theorem l6_gKer_inc (h : ConfHyp F U) {M : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) {K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, ∀ x' ∈ K,
      ‖gKer h δ x - gKer h δ x'‖ ^ 2 ≤ C * ‖x - x'‖ := by
  have hpi := Real.pi_pos
  set M' := max M 1
  have hM1 : 1 ≤ M' := le_max_right _ _
  have hM' : ∀ y ∈ U, ‖deriv F y‖ ≤ M' := fun y hy => (hM y hy).trans (le_max_left _ _)
  obtain ⟨ε, hε, hεK⟩ := exists_dist_compl h.isOpen hK hKU
  have hball : ∀ x ∈ K, ball x ε ⊆ U := fun x hx y hy => by
    by_contra hyU
    have := hεK x hx y hyU
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hy
    linarith
  obtain ⟨d, hd, hdK⟩ := exists_dist_image_compl h hK hKU
  set C₀ := 1 / (Real.pi ^ 2 * d ^ 2)
  set C₁ := C₀ * (Real.pi * 1)
  set K₀ := 10 * M' ^ 4 / Real.pi ^ 2
  have hC₀ : 0 ≤ C₀ := by positivity
  have hK₀ : 0 ≤ K₀ := by positivity
  have hbd : ∀ δ, 0 < δ → ∀ x ∈ K, ‖gKer h δ x‖ ^ 2 ≤ C₁ := fun δ hδ x hx => by
    have := norm_sq_gKer_le h hd hδ (hdK x hx)
    refine this.trans (le_of_eq ?_)
    simp only [C₁, C₀]; field_simp
  refine ⟨4 * C₁ / ε + (4 * C₀ + 2 * K₀) * (Real.pi * 1), fun δ hδ x hx x' hx' => ?_⟩
  set hd' := ‖x - x'‖ with hhd
  have hh0 : 0 ≤ hd' := norm_nonneg _
  have hC₁ : 0 ≤ C₁ := by positivity
  rcases hh0.eq_or_lt with h0 | hpos
  · have : x = x' := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    rw [← h0, this, sub_self, norm_zero]; norm_num
  by_cases hfar : ε ≤ hd'
  · have h1 := norm_sub_sq_le_two (gKer h δ x) (gKer h δ x')
    have h2 : 4 * C₁ ≤ 4 * C₁ / ε * hd' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε]; nlinarith
    nlinarith [hbd δ hδ x hx, hbd δ hδ x' hx', mul_nonneg (by positivity : (0 : ℝ) ≤
      (4 * C₀ + 2 * K₀) * (Real.pi * 1)) hh0]
  push Not at hfar
  have hx'b : x' ∈ ball x ε := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hfar
  have hη : ‖F x - F x'‖ ≤ M' * hd' :=
    norm_F_sub_le (confHyp_mono h isOpen_ball (hball x hx)) (convex_ball x ε)
      (fun z hz => hM' z (hball x hx hz)) (mem_ball_self hε) hx'b
  have hae : ((gKer h δ x - gKer h δ x' : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun p => gKerFun F U δ x p - gKerFun F U δ x' p := by
    filter_upwards [Lp.coeFn_sub (gKer h δ x) (gKer h δ x'), coeFn_gKer h hδ x,
      coeFn_gKer h hδ x'] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hinc : ∀ t z, hd' < t → t ≤ 1 →
      (gKerFun F U δ x (t, z) - gKerFun F U δ x' (t, z)) ^ 2 ≤
        K₀ * hd' ^ 2 / t ^ 3 * (Real.exp (-‖F x - z‖ ^ 2 / (1 * t)) +
          Real.exp (-‖F x' - z‖ ^ 2 / (1 * t))) := by
    intro t z hht ht1
    have ht0 : 0 < t := lt_of_le_of_lt hh0 hht
    have hh2 : hd' ^ 2 ≤ t := by nlinarith
    have hR : 0 ≤ K₀ * hd' ^ 2 / t ^ 3 * (Real.exp (-‖F x - z‖ ^ 2 / (1 * t)) +
        Real.exp (-‖F x' - z‖ ^ 2 / (1 * t))) := by positivity
    simp only [gKerFun]
    by_cases hp : (t, z) ∈ (pushTarget F U)ᶜ
    swap
    · simp only [indicator_of_notMem hp, sub_zero]; simpa using hR
    simp only [indicator_of_mem hp]
    by_cases hA : (t, z) ∈ setA δ
    swap
    · simp only [indicator_of_notMem hA, sub_zero]; simpa using hR
    simp only [indicator_of_mem hA, aHat, one_mul]
    have hMM : 1 ≤ M' ^ 2 := by nlinarith
    exact gauss_sub_sq_le ht0 le_rfl (by nlinarith) hM1 hh2 hη
  have hmain := lintegral_inc_le hC₀ hK₀ one_pos hpos (sq_gKerFun_le hd hδ (hdK x hx))
    (sq_gKerFun_le hd hδ (hdK x' hx')) hinc
  have := norm_sq_le_of_ae hae (fun p => le_rfl) (by positivity) hmain
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * C₁ / ε) hh0]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DDDF Lemma 6, Step 2–3: increments of `φ_L`** (DDDF l. 579, DF Lemma 4.2):
`E(φ_L(x) − φ_L(x'))² ≤ C|x − x'|`, uniformly in `δ > 0` and `x, x' ∈ K`. -/
theorem l6_inc_phiL (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W') :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, ∀ x' ∈ K,
      ∫ ω, (phiL h W W' δ x ω - phiL h W W' δ x' ω) ^ 2 ∂P ≤ C * ‖x - x'‖ := by
  obtain ⟨C₁, hC₁⟩ := l6_lKer_inc h hUb hF1 hM hM2 hK hKU
  obtain ⟨C₂, hC₂⟩ := l6_gKer_inc h hM hK hKU
  refine ⟨2 * Real.pi * (C₁ + C₂), fun δ hδ x hx x' hx' => ?_⟩
  refine (integral_sq_phiL_sub_le h hW hW' δ x x').trans ?_
  have := hC₁ δ hδ x hx x' hx'
  have := hC₂ δ hδ x hx x' hx'
  have hpi := Real.pi_pos
  nlinarith

/-- **DDDF Lemma 6, Step 2–3: variance of `φ_L`** is bounded uniformly in `δ > 0`, `x ∈ K`. -/
theorem l6_var_phiL (h : ConfHyp F U) (hUb : Bornology.IsBounded U)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) {M M₂ : ℝ} (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M)
    (hM2 : ∀ y ∈ U, ‖deriv (deriv F) y‖ ≤ M₂) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W') :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, Var[phiL h W W' δ x; P] ≤ C := by
  obtain ⟨C₁, hC₁⟩ := l6_lKer_bounded h hUb hF1 hM hM2 hK hKU
  obtain ⟨C₂, hC₂⟩ := l6_gKer_bounded h hK hKU
  refine ⟨2 * Real.pi * (C₁ + C₂), fun δ hδ x hx => ?_⟩
  refine (variance_phiL_le h hW hW' δ x).trans ?_
  have := hC₁ δ hδ x hx
  have := hC₂ δ hδ x hx
  have hpi := Real.pi_pos
  nlinarith

end DDDF
end LQGMetric
