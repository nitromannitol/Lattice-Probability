/-
The quantitative half of the Rellich–Kondrachov mollification step.

Given a mollifier kernel `K`, the companion of the topological result
`LatticeProb.Sobolev.IsTestFn.convolution` is the estimate

  `sobolevNormSq d s₀ (fun x => φ x - (φ ⋆ K) x) ≤ C(K) * sobolevNormSq d s φ`

for `s₀ ≤ s`, with the constant `C(K)` the sup over frequencies of
`‖1 - 𝓕K(ξ)‖² (1 + (2π‖ξ‖)²)^{s₀-s}`.  The point of the estimate is that for
the scaled family `K_Λ x = Λ^d K (Λ x)`, `𝓕K_Λ(ξ) = 𝓕K (ξ/Λ)` tends to
`𝓕K 0 = ∫ K = 1`, so `C(K_Λ) → 0` and the mollified family is a net for the
`H^s` unit ball in the `H^{s₀}` norm.

This file proves the estimate.  The three analytic ingredients are:

* the coercion identity
  `↑(φ ⋆[lsmul ℝ ℝ, volume] K) = (↑φ) ⋆[lsmul ℂ ℂ, volume] (↑K)`,
  proved from `ContinuousLinearMap.integral_comp_comm`;
* Mathlib's `Real.fourier_smul_convolution_eq`, giving
  `𝓕 (↑(φ ⋆ K)) = 𝓕(↑φ) * 𝓕(↑K)`;
* the weighted `lintegral` comparison, using `Real.rpow_add` and
  `MeasureTheory.lintegral_const_mul'`.

The scaled-family limit `C(K_Λ) → 0` is a separate, purely real-variable
statement about `𝓕K`; it is recorded at the end of the file.
-/
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory ContinuousLinearMap Set Real
open scoped ENNReal FourierTransform Convolution Pointwise

namespace LatticeProb.Sobolev

variable {d : ℕ}

/-- **Coercion of a real convolution.**  Coercing a real convolution to `ℂ` is the
same as convolving the two coercions with the complex scalar multiplication.  The
proof is the linearity of the integral under the continuous linear map
`Complex.ofRealCLM`, applied to the (integrable) pointwise product. -/
theorem ofReal_convolution (φ K : Space d → ℝ)
    (hφ : Continuous φ) (hK : Continuous K)
    (hφc : HasCompactSupport φ) (x : Space d) :
    ((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℂ)
      = ((fun y => (φ y : ℂ)) ⋆[lsmul ℂ ℂ, volume] (fun y => (K y : ℂ))) x := by
  have hcont : Continuous (fun t : Space d => φ t * K (x - t)) :=
    hφ.mul (hK.comp (continuous_const.sub continuous_id))
  have hsupp : Function.support (fun t : Space d => φ t * K (x - t)) ⊆
      Function.support φ := by
    intro t ht
    by_contra h
    rw [Function.mem_support] at ht
    exact ht (by rw [Function.notMem_support.mp h, zero_mul])
  have hc : HasCompactSupport (fun t : Space d => φ t * K (x - t)) := hφc.mono hsupp
  have hint : Integrable (fun t : Space d => φ t * K (x - t)) volume :=
    hcont.integrable_of_hasCompactSupport hc
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  have hcongr : (∫ t : Space d, (↑(φ t) : ℂ) * ↑(K (x - t)))
      = ∫ t : Space d, ↑(φ t * K (x - t)) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.ofReal_mul]
  rw [hcongr]
  exact (ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint).symm

/-- The complex coercion of a continuous compactly supported real function is integrable. -/
private theorem integrable_ofReal_of_continuous_hasCompactSupport {f : Space d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (f x : ℂ)) volume := by
  refine (Complex.continuous_ofReal.comp hf).integrable_of_hasCompactSupport ?_
  exact hfc.mono fun x hx => by
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])

/-- **Fourier transform is additive on `Space d → ℂ`.**  Mathlib does not register the
`FourierAdd`/`FourierSMul` instances for the function-level transform, so additivity is
extracted from `Real.fourier_eq` and `integral_sub` directly. -/
theorem fourier_sub_apply (Φ Ψ : Space d → ℂ)
    (hΦ : Integrable Φ volume) (hΨ : Integrable Ψ volume) (ξ : Space d) :
    𝓕 (Φ - Ψ) ξ = 𝓕 Φ ξ - 𝓕 Ψ ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Pi.sub_apply, smul_sub]
  · simpa using hΦ
  · simpa using hΨ

/-- **Fourier transform of a coerced real convolution.**  Combining
`ofReal_convolution` with Mathlib's `Real.fourier_smul_convolution_eq`. -/
theorem fourier_ofReal_convolution (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K) (ξ : Space d) :
    𝓕 (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (φ x : ℂ)) ξ * 𝓕 (fun x => (K x : ℂ)) ξ := by
  have hcoe : (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ))
      = (fun x => (φ x : ℂ)) ⋆[lsmul ℂ ℂ, volume] (fun x => (K x : ℂ)) :=
    funext fun x => ofReal_convolution φ K hφ.continuous hK.continuous hφc x
  have hφint : Integrable (fun x => (φ x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hφ.continuous hφc
  have hKint : Integrable (fun x => (K x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hK.continuous hKc
  rw [hcoe, Real.fourier_smul_convolution_eq hφint hKint ξ, smul_eq_mul]

/-- **Fourier transform of the mollification error.**  For smooth compactly supported
`φ, K`,
`𝓕 (↑(φ - φ ⋆ K)) ξ = 𝓕(↑φ) ξ * (1 - 𝓕(↑K) ξ)`. -/
theorem fourier_sub_convolution (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K) (ξ : Space d) :
    𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (φ x : ℂ)) ξ * (1 - 𝓕 (fun x => (K x : ℂ)) ξ) := by
  have hφint : Integrable (fun x => (φ x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hφ.continuous hφc
  have hconvc : Continuous (φ ⋆[lsmul ℝ ℝ, volume] K) :=
    hKc.continuous_convolution_right (L := lsmul ℝ ℝ) hφ.continuous.locallyIntegrable
      hK.continuous
  have hconvk : HasCompactSupport (φ ⋆[lsmul ℝ ℝ, volume] K) :=
    HasCompactSupport.convolution (L := lsmul ℝ ℝ) (μ := volume) hφc hKc
  have hconvvint : Integrable
      (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hconvc hconvk
  have hsub : (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ))
      = (fun x => (φ x : ℂ))
        - fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ) :=
    funext fun x => Complex.ofReal_sub _ _
  rw [hsub, fourier_sub_apply _ _ hφint hconvvint ξ,
    fourier_ofReal_convolution φ K hφ hK hφc hKc ξ]
  ring

/-- **The quantitative mollification bound.**  Let `K` be a mollifier and let `M`
bound `‖1 - 𝓕(↑K) ξ‖² (1 + (2π‖ξ‖)²)^{s₀ - s}` uniformly.  Then the `H^{s₀}`
mollification error is at most `M` times the `H^s` norm of `φ`. -/
theorem sobolevNormSq_sub_convolution_le (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K)
    {s₀ s M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ξ : Space d,
      ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ^ 2
          * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ M) :
    sobolevNormSq d s₀ (fun x => φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x)
      ≤ ENNReal.ofReal M * sobolevNormSq d s φ := by
  have hwpos : ∀ ξ : Space d, 0 < 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := fun ξ => by positivity
  have hpoint : ∀ ξ : Space d,
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ‖ ^ 2
        ≤ M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    rw [fourier_sub_convolution φ K hφ hK hφc hKc ξ, norm_mul]
    have hsplit : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
        = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
          * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
      rw [← Real.rpow_add (hwpos ξ)]; ring_nf
    rw [hsplit]
    calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
            * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ * ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖) ^ 2
        = (‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ^ 2
              * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s))
            * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by ring
      _ ≤ M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hM ξ) (by positivity)
  unfold sobolevNormSq
  calc ∫⁻ ξ : Space d, ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ : Space d, ENNReal.ofReal
          (M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)) :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpoint ξ)
    _ = ENNReal.ofReal M * ∫⁻ ξ : Space d, ENNReal.ofReal
          ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        rw [← lintegral_const_mul' (ENNReal.ofReal M) _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ξ => ENNReal.ofReal_mul hM0

/-- **Concrete form of the mollification bound.**  If the Fourier transform of the
kernel is uniformly within `c` of `1` and `s₀ ≤ s`, then the mollification error is
at most `c²` times the `H^s` norm.  For a normalised mollifier `K` one may take
`c = 1 + ‖K‖_{L¹}`, and for the scaled family `K_Λ` the constant is the scale factor
that drives the low-frequency step. -/
theorem sobolevNormSq_sub_convolution_le_of_fourier_close (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K)
    {s₀ s c : ℝ} (hsc : s₀ ≤ s)
    (hc : ∀ ξ : Space d, ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ≤ c) :
    sobolevNormSq d s₀ (fun x => φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x)
      ≤ ENNReal.ofReal (c ^ 2) * sobolevNormSq d s φ := by
  refine sobolevNormSq_sub_convolution_le (M := c ^ 2) φ K hφ hK hφc hKc
    (sq_nonneg c) fun ξ => ?_
  have hw1 : (1 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 :=
    le_add_of_nonneg_right (sq_nonneg _)
  have hwle : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hw1 (by linarith)
  have hnn : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) :=
    Real.rpow_nonneg (by positivity) _
  calc ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ^ 2
          * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
      ≤ c ^ 2 * 1 := by
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hc ξ) 2) hwle hnn (by positivity)
    _ = c ^ 2 := mul_one _

/-! ### The scaled-kernel limit (remaining)

For the scaled mollifier `K_Λ x = Λ^d K (Λ x)` one has `𝓕 K_Λ ξ = 𝓕 K (ξ / Λ)`,
and `𝓕 K 0 = ∫ K`.  Hence the constant `M(Λ)` of
`sobolevNormSq_sub_convolution_le` satisfies `M(Λ) → 0` as `Λ → ∞`, because
`‖1 - 𝓕 K (ξ/Λ)‖ → 0` pointwise and the weight
`(1 + (2π‖ξ‖)²)^{s₀-s}` decays at infinity.  That limit is a purely
real-variable statement about `𝓕 K` and is not proved here; the algebraic
mollification estimate above is its quantitative core. -/

end LatticeProb.Sobolev
