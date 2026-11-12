/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Tgt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Src
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L12Phi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′, item (2): the maps `F = β ∘ Φ ∘ α⁻¹`

`F(z) = (a'/2 + i b'/2) + (b'/π) · Φ(α⁻¹ z)`. Analytic part: from an open bounded `U₀ ⊃ S_ρ` on
which `Φ` is injective holomorphic with `C⁻¹ ≤ |Φ'| ≤ C`, `|Φ''| ≤ C`, the set `U = α(U₀)` is an
open bounded neighbourhood of `K = α(S_ρ)` on which `F` is injective holomorphic with
`|F'| = (b'/w₀)|Φ'|` and `|F''| = (b'/π)(π/w₀)²|Φ''|`. Crossing part: if `F(K)` lies in the strip
`0 ≤ Im ≤ b'`, `Re F ≤ 0` on `A` and `Re F ≥ a'` on `B`, every path in `F(K)` from `F(A)` to `F(B)`
crosses `[0,a'] × [0,b']` left–right (DDDF Lemma 12 (2), `tightness.tex` l. 753).
-/

namespace LQGMetric.DDDF.L12

open Set Real Metric

/-- `α⁻¹` is complex affine. -/
lemma alphaInv_eq {w₀ H : ℝ} (hw₀ : 0 < w₀) (z : ℂ) :
    alphaInv w₀ H z = (-Complex.I / ((w₀ / π : ℝ) : ℂ)) * z +
      (-(-Complex.I / ((w₀ / π : ℝ) : ℂ)) * ((w₀ / 2 : ℝ) + (H / 2 : ℝ) * Complex.I)) := by
  have hl : w₀ / π ≠ 0 := (div_pos hw₀ Real.pi_pos).ne'
  have hlc : ((w₀ / π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> field_simp <;> ring

lemma alphaInv_alphaS {w₀ H : ℝ} (hw₀ : 0 < w₀) (w : ℂ) : alphaInv w₀ H (alphaS w₀ H w) = w := by
  have hl : w₀ / π ≠ 0 := (div_pos hw₀ Real.pi_pos).ne'
  apply Complex.ext <;> simp [alphaS, alphaInv] <;> field_simp

/-- **Lemma 12′ (2), analytic part.** -/
theorem tgt_analytic {w₀ H a' b' C : ℝ} (hw₀ : 0 < w₀) (hb' : 0 < b') {Φ : ℂ → ℂ}
    {S U₀ : Set ℂ} (hU₀ : IsOpen U₀) (hU₀b : Bornology.IsBounded U₀) (hSU : S ⊆ U₀)
    (hd : DifferentiableOn ℂ Φ U₀) (hinj : InjOn Φ U₀)
    (hC : ∀ w ∈ U₀, C⁻¹ ≤ ‖deriv Φ w‖ ∧ ‖deriv Φ w‖ ≤ C ∧ ‖deriv (deriv Φ) w‖ ≤ C) :
    ∃ U : Set ℂ, IsOpen U ∧ Bornology.IsBounded U ∧ alphaS w₀ H '' S ⊆ U ∧
      DifferentiableOn ℂ (fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
        ((b' / π : ℝ) : ℂ) * Φ (alphaInv w₀ H z)) U ∧
      InjOn (fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
        ((b' / π : ℝ) : ℂ) * Φ (alphaInv w₀ H z)) U ∧
      ∀ z ∈ U, b' / w₀ * C⁻¹ ≤ ‖deriv (fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
          ((b' / π : ℝ) : ℂ) * Φ (alphaInv w₀ H z)) z‖ ∧
        ‖deriv (fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
          ((b' / π : ℝ) : ℂ) * Φ (alphaInv w₀ H z)) z‖ ≤ b' / w₀ * C ∧
        ‖deriv (deriv (fun z => ((a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I) +
          ((b' / π : ℝ) : ℂ) * Φ (alphaInv w₀ H z))) z‖ ≤ b' / w₀ * (π / w₀) * C := by
  set μ : ℂ := -Complex.I / ((w₀ / π : ℝ) : ℂ) with hμ
  set ν : ℂ := -μ * ((w₀ / 2 : ℝ) + (H / 2 : ℝ) * Complex.I) with hν
  set e : ℂ := (a' / 2 : ℝ) + (b' / 2 : ℝ) * Complex.I
  set A : ℂ := ((b' / π : ℝ) : ℂ) with hA
  have hai : alphaInv w₀ H = fun z => μ * z + ν := funext (alphaInv_eq hw₀)
  rw [hai]
  have hl : 0 < w₀ / π := div_pos hw₀ Real.pi_pos
  have hμn : ‖μ‖ = π / w₀ := by
    rw [hμ, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hl.le]
    field_simp
  have hμ0 : μ ≠ 0 := div_ne_zero (neg_ne_zero.2 Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.2 hl.ne')
  have hAn : ‖A‖ = b' / π := by
    rw [hA, Complex.norm_real, Real.norm_of_nonneg (div_pos hb' Real.pi_pos).le]
  have hA0 : A ≠ 0 := Complex.ofReal_ne_zero.2 (div_pos hb' Real.pi_pos).ne'
  set U := (fun z => μ * z + ν) ⁻¹' U₀ with hU
  have haff : Continuous (fun z : ℂ => μ * z + ν) := by fun_prop
  have hUo : IsOpen U := hU₀.preimage haff
  have hder : ∀ z ∈ U, HasDerivAt (fun z => e + A * Φ (μ * z + ν))
      (A * (deriv Φ (μ * z + ν) * (μ * 1))) z := by
    intro z hz
    have h1 : HasDerivAt (fun z : ℂ => μ * z + ν) (μ * 1) z :=
      ((hasDerivAt_id z).const_mul μ).add_const ν
    have h2 := ((hd _ hz).differentiableAt (hU₀.mem_nhds hz)).hasDerivAt
    exact ((h2.comp z h1).const_mul A).const_add e
  have hd1 : DifferentiableOn ℂ (deriv Φ) U₀ := hd.deriv hU₀
  have hder2 : ∀ z ∈ U, deriv (deriv (fun z => e + A * Φ (μ * z + ν))) z =
      A * (deriv (deriv Φ) (μ * z + ν) * (μ * 1)) * (μ * 1) := by
    intro z hz
    have heq : deriv (fun z => e + A * Φ (μ * z + ν)) =ᶠ[nhds z]
        fun z => A * (deriv Φ (μ * z + ν) * (μ * 1)) := by
      filter_upwards [hUo.mem_nhds hz] with y hy using (hder y hy).deriv
    rw [heq.deriv_eq]
    have h1 : HasDerivAt (fun z : ℂ => μ * z + ν) (μ * 1) z :=
      ((hasDerivAt_id z).const_mul μ).add_const ν
    have h2 := ((hd1 _ hz).differentiableAt (hU₀.mem_nhds hz)).hasDerivAt
    exact (((h2.comp z h1).mul_const (μ * 1)).const_mul A).deriv.trans (by ring)
  refine ⟨U, hUo, ?_, ?_, fun z hz => (hder z hz).differentiableAt.differentiableWithinAt,
    ?_, fun z hz => ?_⟩
  · obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hU₀b
    refine (isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨(R + ‖ν‖) / ‖μ‖, fun z hz => ?_⟩
    have := hR hz
    rw [mem_closedBall, dist_zero_right] at this ⊢
    rw [le_div_iff₀ (norm_pos_iff.2 hμ0), mul_comm, ← norm_mul]
    have h3 := norm_sub_le (μ * z + ν) ν
    rw [add_sub_cancel_right] at h3; linarith
  · rintro _ ⟨w, hw, rfl⟩
    show μ * alphaS w₀ H w + ν ∈ U₀
    have h := congrFun hai (alphaS w₀ H w)
    rw [alphaInv_alphaS hw₀] at h
    rw [← h]; exact hSU hw
  · intro x hx y hy hxy
    have h1 : Φ (μ * x + ν) = Φ (μ * y + ν) := by
      have := hxy; simp only at this; exact mul_left_cancel₀ hA0 (add_left_cancel this)
    have h2 := hinj hx hy h1
    exact mul_left_cancel₀ hμ0 (add_right_cancel h2)
  · obtain ⟨c1, c2, c3⟩ := hC _ hz
    have hc : 0 < b' / w₀ := div_pos hb' hw₀
    have hn1 : ‖deriv (fun z => e + A * Φ (μ * z + ν)) z‖ = b' / w₀ * ‖deriv Φ (μ * z + ν)‖ := by
      rw [(hder z hz).deriv, norm_mul, norm_mul, mul_one, hAn, hμn]
      field_simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hn1]; exact mul_le_mul_of_nonneg_left c1 hc.le
    · rw [hn1]; exact mul_le_mul_of_nonneg_left c2 hc.le
    · rw [hder2 z hz, norm_mul, norm_mul, norm_mul, mul_one, hAn, hμn]
      have : b' / π * (‖deriv (deriv Φ) (μ * z + ν)‖ * (π / w₀)) * (π / w₀) =
          b' / w₀ * (π / w₀) * ‖deriv (deriv Φ) (μ * z + ν)‖ := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left c3 (by positivity)

/-- **Lemma 12′ (2), crossing part.** -/
theorem tgt_cross {a' b' : ℝ} (ha' : 0 < a') {F : ℂ → ℂ} {K A B : Set ℂ}
    (hK : ∀ z ∈ K, (F z).im ∈ Icc 0 b') (hA : ∀ z ∈ A, (F z).re ≤ 0)
    (hB : ∀ z ∈ B, a' ≤ (F z).re) {z₀ z₁ : ℂ} (γ : Path z₀ z₁) (hγ : ∀ τ, γ τ ∈ F '' K)
    (h0 : z₀ ∈ F '' A) (h1 : z₁ ∈ F '' B) : RectCross.CrossesLR γ 0 a' 0 b' := by
  have hext : ∀ u : ℝ, γ.extend u ∈ F '' K := by
    intro u
    obtain ⟨τ, hτ⟩ : γ.extend u ∈ range γ := γ.extend_range ▸ mem_range_self u
    rw [← hτ]; exact hγ τ
  have hc : ContinuousOn (fun u => (γ.extend u).re) (Icc 0 1) :=
    (Complex.continuous_re.comp γ.continuous_extend).continuousOn
  obtain ⟨x, hx, rfl⟩ := h0
  obtain ⟨y, hy, rfl⟩ := h1
  obtain ⟨s, t, hs0, hst, ht1, hs, ht, hmid⟩ := RectCross.exists_sub_crossing zero_le_one hc
    ha'.le (by simp only [Path.extend_zero]; exact hA x hx)
    (by simp only [Path.extend_one]; exact hB y hy)
  refine ⟨s, t, hs0, hst, ht1, fun u hu => ⟨hmid u hu, ?_⟩, Or.inl ⟨hs, ht⟩⟩
  obtain ⟨w, hw, he⟩ := hext u
  rw [← he]; exact hK w hw

end LQGMetric.DDDF.L12
