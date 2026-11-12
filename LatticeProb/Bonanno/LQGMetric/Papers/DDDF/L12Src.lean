/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Src at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Geom
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′, item (1): crossings of the small rectangle cross the source domain

Source domain (decision D-B4): `K = α(S_ρ)`, `α(w) = c + iλw`, `λ = w₀/π`, `c = w₀/2 + iH/2`,
i.e. `S_ρ = G(D̄_ρ)` rotated by `π/2` and scaled so that, over the rectangle `[0,w₀] × [0,H]`, its
two long sides `α(G(ρe^{iθ}))` (left) and `α(G(ρe^{−iθ}))` (right) are graphs over the vertical
direction strictly inside the rectangle. Every left–right crossing of the rectangle has a
sub-path inside `K` from the left side to the right side of `K` (DDDF Lemma 12 (1),
`tightness.tex` l. 750; DF Thm 3.1 Step 1, l. 642). Own argument: the sub-path is extracted with
`RectCross.exists_sub_crossing'` applied to `f = Im w / g(Re w)`, `w = α⁻¹(z)` (D-DDDF-14).
-/

namespace LQGMetric.DDDF.L12

open Set Real

/-- The affine map `α(w) = (w₀/2 + iH/2) + i (w₀/π) w`. -/
noncomputable def alphaS (w₀ H : ℝ) (w : ℂ) : ℂ :=
  ((w₀ / 2 : ℝ) + (H / 2 : ℝ) * Complex.I) + Complex.I * ((w₀ / π : ℝ) : ℂ) * w

/-- Its inverse, written in coordinates. -/
noncomputable def alphaInv (w₀ H : ℝ) (z : ℂ) : ℂ :=
  ⟨(z.im - H / 2) / (w₀ / π), -(z.re - w₀ / 2) / (w₀ / π)⟩

lemma alphaS_alphaInv {w₀ H : ℝ} (hw₀ : 0 < w₀) (z : ℂ) : alphaS w₀ H (alphaInv w₀ H z) = z := by
  have hl : w₀ / π ≠ 0 := (div_pos hw₀ Real.pi_pos).ne'
  apply Complex.ext <;> simp [alphaS, alphaInv] <;> field_simp <;> ring

/-- The common numerical facts on the profile over `|u| ≤ U₀`. -/
lemma prof_facts {ρ U₀ u : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hk : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1) (hu : |u| ≤ U₀) :
    0 < (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh u ∧ (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh u < 1 ∧
      0 < gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) u ∧ gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) u < π / 2 ∧
      Real.cos (gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) u) = (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh u := by
  have hkp : 0 < (1 - ρ ^ 2) / (1 + ρ ^ 2) := div_pos (by nlinarith) (by positivity)
  have h0 : 0 < (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh u := mul_pos hkp (Real.cosh_pos u)
  have hU : 0 ≤ U₀ := (abs_nonneg u).trans hu
  have h1 : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh u < 1 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ hkp.le) hk
    rw [Real.cosh_le_cosh, abs_of_nonneg hU]; exact hu
  refine ⟨h0, h1, Real.arccos_pos.2 h1, Real.arccos_lt_pi_div_two.2 h0, ?_⟩
  exact Real.cos_arccos (by linarith) h1.le

/-- Points between the two graphs lie in `S_ρ`. -/
theorem mem_S_of_le {ρ U₀ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hk : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1) {w : ℂ} (hu : |w.re| ≤ U₀)
    (hv : |w.im| ≤ gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) w.re) :
    w ∈ sG '' Metric.closedBall 0 ρ := by
  obtain ⟨-, -, -, hg2, hgc⟩ := prof_facts hρ0 hρ1 hk hu
  have hw : |w.im| < π / 2 := lt_of_le_of_lt hv hg2
  have hc : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh w.re ≤ Real.cos w.im := by
    rw [← hgc, ← Real.cos_abs w.im]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hv
  refine ⟨sT w, ?_, sG_sT hw⟩
  rw [Metric.mem_closedBall, dist_zero_right]; exact norm_sT_le hρ0 hw hc

/-- Points of the upper graph are `G(ρ e^{iθ})`, `θ ∈ [θ₁, π − θ₁]`. -/
theorem top_of_eq {ρ U₀ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hk : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1) {w : ℂ} (hu : |w.re| ≤ U₀)
    (hv : w.im = gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) w.re) :
    ∃ θ ∈ Icc (Real.arccos ((Real.exp (2 * U₀) - 1) / (Real.exp (2 * U₀) + 1) *
        ((1 + ρ ^ 2) / (2 * ρ)))) (π - Real.arccos ((Real.exp (2 * U₀) - 1) /
        (Real.exp (2 * U₀) + 1) * ((1 + ρ ^ 2) / (2 * ρ)))),
      w = sG ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
  obtain ⟨-, -, hg0, hg2, hgc⟩ := prof_facts hρ0 hρ1 hk hu
  have hw : |w.im| < π / 2 := by rw [hv, abs_of_pos hg0]; exact hg2
  obtain ⟨hn, hr⟩ := sT_on_boundary hρ0 hw hu (by rw [hv, hgc])
  obtain ⟨-, him, -⟩ := sT_parts w hw
  have hD : 0 < Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1 := by
    have := cos_pos_of_abs_lt hw; have := Real.exp_pos w.re; positivity
  have hs : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi (by rw [hv]; exact hg0)
    (by rw [hv]; linarith [Real.pi_pos])
  have hi : 0 ≤ (sT w).im := by rw [him]; have := Real.exp_pos w.re; positivity
  obtain ⟨θ, hθ, he⟩ := exists_angle hρ0 hn hi hr
  exact ⟨θ, hθ, by rw [← he, sG_sT hw]⟩

/-- Points of the lower graph are `G(ρ e^{−iθ})`, `θ ∈ [θ₁, π − θ₁]`. -/
theorem bot_of_eq {ρ U₀ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hk : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1) {w : ℂ} (hu : |w.re| ≤ U₀)
    (hv : w.im = -gProf ((1 - ρ ^ 2) / (1 + ρ ^ 2)) w.re) :
    ∃ θ ∈ Icc (Real.arccos ((Real.exp (2 * U₀) - 1) / (Real.exp (2 * U₀) + 1) *
        ((1 + ρ ^ 2) / (2 * ρ)))) (π - Real.arccos ((Real.exp (2 * U₀) - 1) /
        (Real.exp (2 * U₀) + 1) * ((1 + ρ ^ 2) / (2 * ρ)))),
      w = sG ((ρ : ℂ) * Complex.exp ((-θ : ℝ) * Complex.I)) := by
  obtain ⟨-, -, hg0, hg2, hgc⟩ := prof_facts hρ0 hρ1 hk hu
  have hw : |w.im| < π / 2 := by rw [hv, abs_neg, abs_of_pos hg0]; exact hg2
  obtain ⟨hn, hr⟩ := sT_on_boundary hρ0 hw hu (by rw [hv, Real.cos_neg, hgc])
  obtain ⟨-, him, -⟩ := sT_parts w hw
  have hD : 0 < Real.exp w.re ^ 2 + 2 * Real.exp w.re * Real.cos w.im + 1 := by
    have := cos_pos_of_abs_lt hw; have := Real.exp_pos w.re; positivity
  have hs : Real.sin w.im < 0 := by
    rw [hv, Real.sin_neg, neg_lt_zero]
    exact Real.sin_pos_of_pos_of_lt_pi hg0 (by linarith [Real.pi_pos])
  have hi : 0 ≤ ((starRingEnd ℂ) (sT w)).im := by
    rw [Complex.conj_im, him, neg_nonneg]
    apply div_nonpos_of_nonpos_of_nonneg _ hD.le
    have := Real.exp_pos w.re; nlinarith
  have hn' : ‖(starRingEnd ℂ) (sT w)‖ = ρ := by rw [Complex.norm_conj, hn]
  have hr' := hr
  rw [← Complex.conj_re] at hr'
  obtain ⟨θ, hθ, he⟩ := exists_angle hρ0 hn' hi hr'
  refine ⟨θ, hθ, ?_⟩
  have : sT w = (ρ : ℂ) * Complex.exp ((-θ : ℝ) * Complex.I) := by
    rw [← Complex.conj_conj (sT w), he, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring_nf
  rw [← this, sG_sT hw]

@[simp] lemma alphaInv_re (w₀ H : ℝ) (z : ℂ) : (alphaInv w₀ H z).re = (z.im - H / 2) / (w₀ / π) :=
  rfl

@[simp] lemma alphaInv_im (w₀ H : ℝ) (z : ℂ) :
    (alphaInv w₀ H z).im = -(z.re - w₀ / 2) / (w₀ / π) := rfl

lemma continuous_gProf (k : ℝ) : Continuous (gProf k) :=
  Real.continuous_arccos.comp (continuous_const.mul Real.continuous_cosh)

/-- The angle threshold `c₀ = (Q−1)/(Q+1) · (1+ρ²)/(2ρ)`, `Q = e^{2U₀}`; `θ₁ = arccos c₀`. -/
noncomputable def cZero (ρ U₀ : ℝ) : ℝ :=
  (Real.exp (2 * U₀) - 1) / (Real.exp (2 * U₀) + 1) * ((1 + ρ ^ 2) / (2 * ρ))

/-- **Lemma 12′ (1), source side.** Every left–right crossing of `[0,w₀] × [0,H]` has a sub-path
inside `K = α(S_ρ)` from the left side `α(G(ρe^{iθ}))` to the right side `α(G(ρe^{−iθ'}))`,
`θ, θ' ∈ [θ₁, π − θ₁]`. -/
theorem src_crossing {ρ U₀ w₀ H : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hw₀ : 0 < w₀) (hH : 0 < H)
    (hU : π * H / (2 * w₀) ≤ U₀) (hk : (1 - ρ ^ 2) / (1 + ρ ^ 2) * Real.cosh U₀ < 1)
    {p q : ℂ} (γ : Path p q) (hγ : ∀ τ, γ τ ∈ RectCross.rect 0 w₀ 0 H) (hp : p.re = 0)
    (hq : q.re = w₀) :
    ∃ s t θ θ' : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
      (∀ u ∈ Icc s t, γ.extend u ∈ alphaS w₀ H '' (sG '' Metric.closedBall 0 ρ)) ∧
      θ ∈ Icc (Real.arccos (cZero ρ U₀)) (π - Real.arccos (cZero ρ U₀)) ∧
      θ' ∈ Icc (Real.arccos (cZero ρ U₀)) (π - Real.arccos (cZero ρ U₀)) ∧
      γ.extend s = alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ∧
      γ.extend t = alphaS w₀ H (sG ((ρ : ℂ) * Complex.exp ((-θ' : ℝ) * Complex.I))) := by
  set k := (1 - ρ ^ 2) / (1 + ρ ^ 2) with hkdef
  have hl : 0 < w₀ / π := div_pos hw₀ Real.pi_pos
  have hrect : ∀ u : ℝ, γ.extend u ∈ RectCross.rect 0 w₀ 0 H := by
    intro u
    obtain ⟨τ, hτ⟩ : γ.extend u ∈ range γ := γ.extend_range ▸ mem_range_self u
    rw [← hτ]; exact hγ τ
  have hre : ∀ u : ℝ, |(alphaInv w₀ H (γ.extend u)).re| ≤ U₀ := by
    intro u
    obtain ⟨-, h1, h2⟩ := hrect u
    rw [alphaInv_re, abs_div, abs_of_pos hl, div_le_iff₀ hl]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hU hl.le)
    have : π * H / (2 * w₀) * (w₀ / π) = H / 2 := by field_simp
    rw [this, abs_le]; constructor <;> linarith
  have hg : ∀ u : ℝ, 0 < gProf k (alphaInv w₀ H (γ.extend u)).re := fun u =>
    (prof_facts hρ0 hρ1 hk (hre u)).2.2.1
  have hg2 : ∀ u : ℝ, gProf k (alphaInv w₀ H (γ.extend u)).re < π / 2 := fun u =>
    (prof_facts hρ0 hρ1 hk (hre u)).2.2.2.1
  set F : ℝ → ℝ := fun u => (alphaInv w₀ H (γ.extend u)).im /
    gProf k (alphaInv w₀ H (γ.extend u)).re with hF
  have hFc : ContinuousOn F (Icc 0 1) := by
    apply Continuous.continuousOn
    apply Continuous.div _ _ (fun u => (hg u).ne')
    · simp only [alphaInv_im]
      exact ((Complex.continuous_re.comp γ.continuous_extend).sub continuous_const).neg.div_const _
    · simp only [alphaInv_re]
      exact (continuous_gProf k).comp
        (((Complex.continuous_im.comp γ.continuous_extend).sub continuous_const).div_const _)
  have hF0 : 1 ≤ F 0 := by
    simp only [hF, Path.extend_zero, alphaInv_im, hp]
    have h0 := hg 0
    have h0' := hg2 0
    rw [Path.extend_zero] at h0 h0'
    rw [le_div_iff₀ h0, one_mul]
    have : -(0 - w₀ / 2) / (w₀ / π) = π / 2 := by field_simp; ring
    rw [this]; exact h0'.le
  have hF1 : F 1 ≤ -1 := by
    simp only [hF, Path.extend_one, alphaInv_im, hq]
    have h0 := hg 1
    have h0' := hg2 1
    rw [Path.extend_one] at h0 h0'
    rw [div_le_iff₀ h0]
    have : -(w₀ - w₀ / 2) / (w₀ / π) = -(π / 2) := by field_simp; ring
    rw [this]; linarith
  obtain ⟨s, t, hs0, hst, ht1, hFs, hFt, hmid⟩ :=
    RectCross.exists_sub_crossing' zero_le_one hFc (by norm_num : (-1 : ℝ) ≤ 1) hF0 hF1
  have hz : ∀ u : ℝ, alphaS w₀ H (alphaInv w₀ H (γ.extend u)) = γ.extend u := fun u =>
    alphaS_alphaInv hw₀ _
  refine ⟨s, t, ?_⟩
  obtain ⟨θ, hθ, hθe⟩ := top_of_eq hρ0 hρ1 hk (hre s)
    (by have := hFs; simp only [hF] at this; exact (div_eq_one_iff_eq (hg s).ne').1 this)
  obtain ⟨θ', hθ', hθe'⟩ := bot_of_eq hρ0 hρ1 hk (hre t)
    (by have := hFt; simp only [hF] at this; rw [div_eq_iff (hg t).ne'] at this; linarith)
  refine ⟨θ, θ', hs0, hst, ht1, fun u hu => ?_, hθ, hθ', ?_, ?_⟩
  · have h1 := hmid u hu
    simp only [hF] at h1
    have : |(alphaInv w₀ H (γ.extend u)).im| ≤ gProf k (alphaInv w₀ H (γ.extend u)).re := by
      have h2 : |(alphaInv w₀ H (γ.extend u)).im / gProf k (alphaInv w₀ H (γ.extend u)).re| ≤ 1 :=
        abs_le.2 h1
      rwa [abs_div, abs_of_pos (hg u), div_le_one (hg u)] at h2
    rw [← hz u]
    exact mem_image_of_mem _ (mem_S_of_le hρ0 hρ1 hk (hre u) this)
  · rw [← hz s, ← hθe]
  · rw [← hz t, ← hθe']

end LQGMetric.DDDF.L12
