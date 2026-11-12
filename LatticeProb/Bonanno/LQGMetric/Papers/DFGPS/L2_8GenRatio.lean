/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GenRatio at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, general squares: the normalization ratio `𝔞_{ε/s} / 𝔞_ε ≍ 1`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:893–894) reduce Lemma 2.8 to
`S = [0,1]²` "by Lemma 2.6 and the scale and translation invariance of the law of `h`". After the
rescaling `z ↦ a + s z` the normalization changes from `𝔞_ε` to `𝔞_{ε/s}`; the paper does not
comment on this. Decision D73 (DECISIONS.md): the ratio is bounded using `𝔞_ε ≍ λ_ε`
(`aEps_lambda_bounds`, DFGPS T:888–891) and DDDF (6.99) (`Blueprint.DDDFEq6_99`,
Ding–Dubédat–Dunlap–Falconet, `eq:MulCont`, DD:1615–1621):
`λ_{δδ'} ≍ λ_δ λ_{δ'}` up to `C e^{C√|log max(δ,δ')|}`, which is bounded for `δ' ∈ {s, 1/s}`
fixed and `δ < δ'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

/-- From the quasi-multiplicativity (6.99): `Λ(δ t) ≍ Λ(δ)` for fixed `t ∈ (0,1)` and small `δ`. -/
theorem ratio_of_mulCont {Λ : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hM : ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ δ' ∈ Ioo (0 : ℝ) 1,
      C⁻¹ * Real.exp (-C * Real.sqrt |Real.log (max δ δ')|) * (Λ δ * Λ δ') ≤ Λ (δ * δ') ∧
      Λ (δ * δ') ≤ C * Real.exp (C * Real.sqrt |Real.log (max δ δ')|) * (Λ δ * Λ δ'))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {εb : ℝ} (hεb : 0 < εb)
    (hpos : ∀ δ, 0 < δ → δ < εb → 0 < Λ δ) :
    ∃ K > 0, ∀ δ, 0 < δ → δ < min εb t → K⁻¹ * Λ δ ≤ Λ (δ * t) ∧ Λ (δ * t) ≤ K * Λ δ := by
  set c₁ := C⁻¹ * Real.exp (-C * Real.sqrt |Real.log t|)
  set c₂ := C * Real.exp (C * Real.sqrt |Real.log t|)
  have hc₁ : 0 < c₁ := by positivity
  have hc₂ : 0 < c₂ := by positivity
  have hm : 0 < min εb t := lt_min hεb ht.1
  have hmax : ∀ δ, δ < min εb t → max δ t = t := fun δ hδ =>
    max_eq_right (hδ.trans_le (min_le_right _ _)).le
  have hδ1 : ∀ δ, 0 < δ → δ < min εb t → δ ∈ Ioo (0 : ℝ) 1 := fun δ h0 hδ =>
    ⟨h0, (hδ.trans_le (min_le_right _ _)).trans ht.2⟩
  have hδt : ∀ δ, 0 < δ → δ < min εb t → δ * t < εb := fun δ h0 hδ =>
    lt_of_le_of_lt (mul_le_of_le_one_right h0.le ht.2.le) (hδ.trans_le (min_le_left _ _))
  -- `Λ t > 0`
  set δ₀ := min εb t / 2
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₀m : δ₀ < min εb t := by simp only [δ₀]; linarith
  have hΛt : 0 < Λ t := by
    have h1 := hpos _ (mul_pos hδ₀ ht.1) (hδt _ hδ₀ hδ₀m)
    have h2 := (hM _ (hδ1 _ hδ₀ hδ₀m) t ht).2
    rw [hmax _ hδ₀m] at h2
    have h3 := hpos _ hδ₀ (hδ₀m.trans_le (min_le_left _ _))
    by_contra hneg
    push Not at hneg
    have : c₂ * (Λ δ₀ * Λ t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc₂.le (mul_nonpos_of_nonneg_of_nonpos h3.le hneg)
    linarith
  refine ⟨max (c₂ * Λ t) (c₁ * Λ t)⁻¹, lt_max_of_lt_left (by positivity),
    fun δ h0 hδ => ?_⟩
  have hΛδ := hpos _ h0 (hδ.trans_le (min_le_left _ _))
  have hb := hM _ (hδ1 _ h0 hδ) t ht
  rw [hmax _ hδ] at hb
  constructor
  · have hK : (max (c₂ * Λ t) (c₁ * Λ t)⁻¹)⁻¹ ≤ c₁ * Λ t := by
      rw [inv_le_comm₀ (lt_max_of_lt_left (by positivity)) (by positivity)]
      exact le_max_right _ _
    calc (max (c₂ * Λ t) (c₁ * Λ t)⁻¹)⁻¹ * Λ δ ≤ c₁ * Λ t * Λ δ :=
          mul_le_mul_of_nonneg_right hK hΛδ.le
      _ = c₁ * (Λ δ * Λ t) := by ring
      _ ≤ Λ (δ * t) := hb.1
  · calc Λ (δ * t) ≤ c₂ * (Λ δ * Λ t) := hb.2
      _ = c₂ * Λ t * Λ δ := by ring
      _ ≤ max (c₂ * Λ t) (c₁ * Λ t)⁻¹ * Λ δ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hΛδ.le

end LQGMetric.DFGPS
