/-
# The band-limited Bernstein bound

The second missing input of the low-frequency net `rkLowFreqNet` is a uniform
`Cᵐ` bound for band-limited Schwartz functions: a function whose Fourier
transform vanishes beyond `2Λ` and whose `H^s` norm is at most `1` has all its
derivatives up to order `m` bounded by a constant depending only on `d`, `Λ`, `s`
and `m`.  This is the analytic step that makes the band-limited family
`Cᵐ`-precompact.

The mechanism is the inverse Fourier representation on the band.  A Schwartz
function `ψ` whose Fourier transform vanishes for `2Λ ≤ ‖ξ‖` satisfies

`𝓕⁻ ψ x = ∫_{‖ξ‖ ≤ 2Λ} 𝐞 ⟪ξ, x⟫ • ψ ξ dξ`,

because the Fourier-inversion integral only sees the band.  Differentiating under
the integral multiplies the integrand by the `k`-fold tensor power of `2πi ξ`,
whose operator norm is `(2π‖ξ‖)^k`, so

`‖D^k (𝓕⁻ ψ) x‖ ≤ ∫_{‖ξ‖ ≤ 2Λ} (2π‖ξ‖)^k ‖ψ ξ‖ dξ`
`≤ (2π·2Λ)^k ∫_{‖ξ‖ ≤ 2Λ} ‖ψ ξ‖ dξ`.

Mathlib's `VectorFourier.iteratedFDeriv_fourierIntegral` performs the
differentiation and `VectorFourier.norm_fourierPowSMulRight_le` bounds the tensor
power.

The remaining step to the consumed `L²` form is the Cauchy–Schwarz comparison
`∫_{‖ξ‖≤2Λ} ‖ψ ξ‖ dξ ≤ (volume (ball 0 (2Λ)))^{1/2} (∫ ‖ψ‖²)^{1/2}` together with
Plancherel; the statements below are therefore in the `L¹`-on-the-band form, and
the `L²` upgrade is the named remaining gap (see
`~/fleet/audit/lib-bandlimited-bernstein.md`).
-/
import LatticeProb.Analysis.Sobolev.FrequencyTruncation

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace

namespace LatticeProb.Sobolev

/-- **Fourier inversion on the band.**  If `ψ` vanishes for `2Λ ≤ ‖ξ‖` then the
inverse Fourier integral of `ψ` only sees the ball of radius `2Λ`. -/
theorem fourierInv_eq_setIntegral {d : ℕ} (ψ : 𝓢(Space d, ℂ)) {Λ : ℝ}
    (hψ : ∀ ξ : Space d, 2 * Λ ≤ ‖ξ‖ → ψ ξ = 0) (x : Space d) :
    𝓕⁻ ψ x = ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), 𝐞 ⟪ξ, x⟫ • ψ ξ := by
  rw [SchwartzMap.fourierInv_coe ψ, Real.fourierInv_eq]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
  have h2 : 2 * Λ ≤ ‖ξ‖ := by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hξ
    exact hξ
  rw [hψ ξ h2, smul_zero]

/-- The `L¹` norm on the band of `fourierPowSMulRight (-innerSL) ψ · k` is at most
`(2π)^k (2Λ)^k` times the `L¹` norm of `ψ` there. -/
private theorem norm_fourierPowSMulRight_band_le {d : ℕ} (ψ : 𝓢(Space d, ℂ))
    (k : ℕ) (ξ : Space d) :
    ‖VectorFourier.fourierPowSMulRight
        ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) ξ k‖
      ≤ (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ := by
  refine (VectorFourier.norm_fourierPowSMulRight_le
    ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) ξ k).trans ?_
  have hL : ‖(-(innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro m
    have h1 : ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) m
        = -(((innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ) m) := by
      simp only [neg_apply]
    rw [h1, norm_neg]
    have h2 := (innerSL ℝ).le_opNorm m
    have h3 := norm_innerSL_le (𝕜 := ℝ) (E := Space d)
    nlinarith [norm_nonneg m, h2, h3]
  have h1 : (2 * Real.pi * ‖(-(innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ)‖) ^ k
      ≤ (2 * Real.pi) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.pi_pos,
      norm_nonneg (-(innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ)]
  calc (2 * Real.pi * ‖(-(innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ)‖) ^ k
        * ‖ξ‖ ^ k * ‖ψ ξ‖
      ≤ (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **The band-limited derivative bound.**  For a Schwartz function `ψ` vanishing
beyond `2Λ`, every derivative of the inverse Fourier transform `𝓕⁻ ψ` is bounded
by `(2π·2Λ)^k` times the `L¹` integral of `ψ` over the band. -/
theorem norm_iteratedFDeriv_fourierInv_le_setIntegral {d : ℕ} (ψ : 𝓢(Space d, ℂ))
    {Λ : ℝ} (hψ : ∀ ξ : Space d, 2 * Λ ≤ ‖ξ‖ → ψ ξ = 0) (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (fun y => 𝓕⁻ ψ y) x‖
      ≤ (2 * Real.pi) ^ k * (2 * Λ) ^ k
          * ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖ψ ξ‖ := by
  have hfun : (fun y : Space d => 𝓕⁻ ψ y)
      = VectorFourier.fourierIntegral 𝐞 volume
          ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ).toLinearMap₁₂
          (fun ξ => ψ ξ) := by
    funext y
    rw [SchwartzMap.fourierInv_coe ψ, Real.fourierInv_eq]
    simp only [VectorFourier.fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply,
      neg_apply, innerSL_apply_apply, neg_neg]
  rw [hfun]
  rw [VectorFourier.iteratedFDeriv_fourierIntegral
    (L := (-(innerSL ℝ) : Space d →L[ℝ] Space d →L[ℝ] ℝ)) (f := fun ξ => ψ ξ)
    (μ := volume) (N := ⊤) (fun n _ => ψ.integrable_pow_mul volume n)
    (ψ.continuous.aestronglyMeasurable) (le_top : ((k : ℕ∞)) ≤ ⊤)]
  have hpt : ∀ ξ : Space d,
      ‖VectorFourier.fourierPowSMulRight
          ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) ξ k‖
        ≤ (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ :=
    fun ξ => norm_fourierPowSMulRight_band_le ψ k ξ
  have h1 : ∫ ξ, ‖VectorFourier.fourierPowSMulRight
        ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) ξ k‖
      ≤ ∫ ξ, (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
      (by simpa only [mul_assoc] using
        (ψ.integrable_pow_mul volume k).const_mul ((2 * Real.pi) ^ k))
      (Filter.Eventually.of_forall hpt)
  have h2 : ∫ ξ, (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖
      = ∫ ξ in Metric.ball 0 (2 * Λ), (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
    have hmem : 2 * Λ ≤ ‖ξ‖ := by
      rw [Metric.mem_ball, dist_zero_right, not_lt] at hξ
      exact hξ
    simp only [hψ ξ hmem, norm_zero, mul_zero]
  have h3 : ∀ ξ ∈ Metric.ball (0 : Space d) (2 * Λ),
      (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖
        ≤ (2 * Real.pi) ^ k * (2 * Λ) ^ k * ‖ψ ξ‖ := by
    intro ξ hξ
    have hξ' : ‖ξ‖ ≤ 2 * Λ := by
      rw [Metric.mem_ball, dist_zero_right] at hξ
      exact hξ.le
    have hpow : ‖ξ‖ ^ k ≤ (2 * Λ) ^ k := pow_le_pow_left₀ (norm_nonneg _) hξ' k
    have hc : (0 : ℝ) ≤ (2 * Real.pi) ^ k := by positivity
    calc (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖
        = (2 * Real.pi) ^ k * (‖ξ‖ ^ k * ‖ψ ξ‖) := by ring
      _ ≤ (2 * Real.pi) ^ k * ((2 * Λ) ^ k * ‖ψ ξ‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hc
      _ = (2 * Real.pi) ^ k * (2 * Λ) ^ k * ‖ψ ξ‖ := by ring
  have h4 : ∫ ξ in Metric.ball 0 (2 * Λ), (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖
      ≤ (2 * Real.pi) ^ k * (2 * Λ) ^ k * ∫ ξ in Metric.ball 0 (2 * Λ), ‖ψ ξ‖ := by
    calc ∫ ξ in Metric.ball 0 (2 * Λ), (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖
        ≤ ∫ ξ in Metric.ball 0 (2 * Λ), (2 * Real.pi) ^ k * (2 * Λ) ^ k * ‖ψ ξ‖ := by
          apply integral_mono_ae
          · have h : Integrable (fun x => (2 * Real.pi) ^ k * ‖x‖ ^ k * ‖ψ x‖) volume := by
              simpa only [mul_assoc] using
                (ψ.integrable_pow_mul volume k).const_mul ((2 * Real.pi) ^ k)
            exact h.integrableOn
          · have h : Integrable
                (fun x => (2 * Real.pi) ^ k * (2 * Λ) ^ k * ‖ψ x‖) volume :=
              ψ.integrable.norm.const_mul ((2 * Real.pi) ^ k * (2 * Λ) ^ k)
            exact h.integrableOn
          · filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
            exact h3 ξ hξ
      _ = (2 * Real.pi) ^ k * (2 * Λ) ^ k * ∫ ξ in Metric.ball 0 (2 * Λ), ‖ψ ξ‖ :=
          integral_const_mul _ _
  calc ‖VectorFourier.fourierIntegral 𝐞 volume
        ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ).toLinearMap₁₂
        (fun v => VectorFourier.fourierPowSMulRight
          ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) v k) x‖
      ≤ ∫ ξ, ‖VectorFourier.fourierPowSMulRight
          ((-(innerSL ℝ)) : Space d →L[ℝ] Space d →L[ℝ] ℝ) (fun ξ => ψ ξ) ξ k‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ, (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ := h1
    _ = ∫ ξ in Metric.ball 0 (2 * Λ), (2 * Real.pi) ^ k * ‖ξ‖ ^ k * ‖ψ ξ‖ := h2
    _ ≤ (2 * Real.pi) ^ k * (2 * Λ) ^ k * ∫ ξ in Metric.ball 0 (2 * Λ), ‖ψ ξ‖ := h4

/-- **The band-limited Bernstein bound for the truncation `P_Λ`.**  For every
order `k` there is `C ≥ 0` such that the `k`-th derivative of `bandTrunc d Λ F`
is at most `C` times the `L¹` norm on the band of `𝓕 F`, uniformly in `F` and in
the point. -/
theorem exists_iteratedFDeriv_bandTrunc_le {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : 𝓢(Space d, ℂ)) (x : Space d),
      ‖iteratedFDeriv ℝ k (fun y => bandTrunc d Λ hΛ.ne' F y) x‖
        ≤ C * ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖𝓕 F ξ‖ := by
  refine ⟨(2 * Real.pi) ^ k * (2 * Λ) ^ k, by positivity, fun F x => ?_⟩
  set ψ : 𝓢(Space d, ℂ) := SchwartzMap.smulLeftCLM ℂ (bandCut d Λ) (𝓕 F) with hψ
  have htr : bandTrunc d Λ hΛ.ne' F = 𝓕⁻ ψ := by
    rw [hψ, bandTrunc, SchwartzMap.fourierMultiplierCLM_apply]
  have hbl : ∀ ξ : Space d, 2 * Λ ≤ ‖ξ‖ → ψ ξ = 0 := by
    intro ξ hξ
    rw [hψ, SchwartzMap.smulLeftCLM_apply (bandCut_temperate d Λ hΛ.ne')]
    change bandCut d Λ ξ • (𝓕 F) ξ = 0
    rw [bandCut_eq_zero d Λ hΛ hξ, zero_smul]
  have hbound := norm_iteratedFDeriv_fourierInv_le_setIntegral ψ hbl k x
  rw [htr]
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine integral_mono_ae (ψ.integrable.norm).integrableOn
    ((𝓕 F).integrable.norm).integrableOn ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with ξ _
  rw [hψ, SchwartzMap.smulLeftCLM_apply (bandCut_temperate d Λ hΛ.ne')]
  change ‖bandCut d Λ ξ • (𝓕 F) ξ‖ ≤ ‖𝓕 F ξ‖
  rw [norm_smul, Real.norm_of_nonneg (bandCut_nonneg d Λ ξ)]
  calc bandCut d Λ ξ * ‖𝓕 F ξ‖ ≤ 1 * ‖𝓕 F ξ‖ :=
        mul_le_mul_of_nonneg_right (bandCut_le_one d Λ ξ) (norm_nonneg _)
    _ = ‖𝓕 F ξ‖ := one_mul _

end LatticeProb.Sobolev
