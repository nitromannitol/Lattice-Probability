/-
# Assembly of the `H^s`–`H^{−s}` duality bound

For real `f, g ∈ L¹ ∩ L²` with finite Sobolev norms of orders `s` and `-s`,
`ofReal (|∫ f g|²) ≤ ‖f‖²_{H^s} ‖g‖²_{H^{−s}}`.  The proof composes Plancherel in `∫⁻`/`ofReal`
form (`abs_integral_mul_le_lintegral_fourier`) with the Cauchy–Schwarz inequality in `∫⁻`
(`ENNReal.lintegral_mul_le_Lp_mul_Lq` at the exponents `2, 2`), applied to the factors
`√w_s ‖𝓕f‖` and `(√w_s)⁻¹ ‖𝓕g‖`.

The `L¹ ∩ L²` hypotheses cannot be dropped: for a non-integrable `f` the pointwise Fourier
integral is `0`, so `sobolevNormSq d s f = 0` while `∫ f f` can be positive, e.g. for
`f x = 1 / (1 + |x|)` on `ℝ`.
-/
import LatticeProb.Analysis.Sobolev.PlancherelPackaging
import LatticeProb.Analysis.Sobolev.SobolevToReal
import LatticeProb.Analysis.Sobolev.SobolevYoungConvolution

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The Sobolev weight is continuous. -/
theorem continuous_sobolevWeight {d : ℕ} (s : ℝ) :
    Continuous (fun ξ : Space d => sobolevWeight s ξ) := by
  unfold sobolevWeight
  refine Continuous.rpow_const (by fun_prop) fun ξ => Or.inl ?_
  positivity

/-- The pointwise Fourier transform of an integrable real function is continuous. -/
theorem continuous_fourier_lift {d : ℕ} {f : Space d → ℝ} (hf1 : Integrable f) :
    Continuous (𝓕 (fun x => (f x : ℂ))) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf1.ofReal

/-- **Cauchy–Schwarz in `∫⁻` at the Sobolev weights.**  For integrable real `f, g`, the Fourier
pairing `∫⁻ ofReal (‖𝓕f‖ ‖𝓕g‖)` is bounded by the square roots of the two Sobolev norms. -/
theorem lintegral_fourier_pairing_le {d : ℕ} (s : ℝ) {f g : Space d → ℝ}
    (hf1 : Integrable f) (hg1 : Integrable g) :
    ∫⁻ ξ : Space d, ENNReal.ofReal (‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖)
      ≤ (sobolevNormSq d s f) ^ ((1 : ℝ) / 2) * (sobolevNormSq d (-s) g) ^ ((1 : ℝ) / 2) := by
  have hcf := continuous_fourier_lift hf1
  have hcg := continuous_fourier_lift hg1
  have hw : ∀ ξ : Space d, 0 < sobolevWeight s ξ := fun ξ =>
    Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)) s
  have hwneg : ∀ ξ : Space d, sobolevWeight (-s) ξ = (sobolevWeight s ξ)⁻¹ := fun ξ => by
    unfold sobolevWeight
    exact Real.rpow_neg (by positivity) s
  have hws : Continuous (fun ξ : Space d => Real.sqrt (sobolevWeight s ξ)) :=
    (continuous_sobolevWeight s).sqrt
  have hsq : ∀ ξ : Space d, 0 < Real.sqrt (sobolevWeight s ξ) := fun ξ =>
    Real.sqrt_pos_of_pos (hw ξ)
  set A : Space d → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (Real.sqrt (sobolevWeight s ξ) * ‖𝓕 (fun x => (f x : ℂ)) ξ‖) with hA
  set B : Space d → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal ((Real.sqrt (sobolevWeight s ξ))⁻¹ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖) with hB
  have hAm : AEMeasurable A volume :=
    (ENNReal.measurable_ofReal.comp (hws.mul hcf.norm).measurable).aemeasurable
  have hBm : AEMeasurable B volume :=
    (ENNReal.measurable_ofReal.comp
      ((hws.inv₀ (fun ξ => (hsq ξ).ne')).mul hcg.norm).measurable).aemeasurable
  have hpt : ∀ ξ : Space d,
      ENNReal.ofReal (‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖)
        = (A * B) ξ := by
    intro ξ
    have h1 : 0 ≤ Real.sqrt (sobolevWeight s ξ) * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ :=
      mul_nonneg (hsq ξ).le (norm_nonneg _)
    simp only [Pi.mul_apply, hA, hB]
    rw [← ENNReal.ofReal_mul h1]
    congr 1
    have := (hsq ξ).ne'
    field_simp
  have hAsq : ∫⁻ ξ, A ξ ^ (2 : ℝ) = sobolevNormSq d s f := by
    rw [sobolevNormSq_eq_lintegral_weight]
    refine lintegral_congr fun ξ => ?_
    simp only [hA]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (hsq ξ).le (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow, Real.sq_sqrt (hw ξ).le]
  have hBsq : ∫⁻ ξ, B ξ ^ (2 : ℝ) = sobolevNormSq d (-s) g := by
    rw [sobolevNormSq_eq_lintegral_weight]
    refine lintegral_congr fun ξ => ?_
    simp only [hB]
    rw [ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (inv_nonneg.mpr (hsq ξ).le) (norm_nonneg _)) (by norm_num),
      Real.rpow_two, mul_pow, inv_pow, Real.sq_sqrt (hw ξ).le, hwneg]
  calc _ = ∫⁻ ξ, (A * B) ξ := lintegral_congr hpt
    _ ≤ (∫⁻ ξ, A ξ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ ξ, B ξ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hAm hBm
    _ = _ := by rw [hAsq, hBsq]

/-- **The `H^s`–`H^{−s}` duality bound** for real `f, g ∈ L¹ ∩ L²` with finite Sobolev norms. -/
theorem sobolevDualityBound_of_memLp {d : ℕ} (s : ℝ) {f g : Space d → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hf1 : Integrable f) (hg1 : Integrable g) :
    ENNReal.ofReal (|∫ x, f x * g x| ^ 2) ≤ sobolevNormSq d s f * sobolevNormSq d (-s) g := by
  have h1 := (abs_integral_mul_le_lintegral_fourier hf hg hf1 hg1).trans
    (lintegral_fourier_pairing_le s hf1 hg1)
  rw [ENNReal.ofReal_pow (abs_nonneg _)]
  calc _ ≤ ((sobolevNormSq d s f) ^ ((1 : ℝ) / 2)
        * (sobolevNormSq d (-s) g) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' h1 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast
          (sobolevNormSq d (-s) g ^ ((1 : ℝ) / 2)), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- **Finite Sobolev norm gives integrability of the weighted Fourier modulus.**  For an
integrable real `f` the weighted squared Fourier modulus is continuous, hence measurable, and its
`∫⁻` is the finite number `sobolevNormSq d s f`. -/
theorem integrable_sobolevWeight_mul_norm_sq {d : ℕ} (s : ℝ) {f : Space d → ℝ}
    (hf1 : Integrable f) (hfin : sobolevNormSq d s f < ⊤) :
    Integrable (fun ξ : Space d => sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) := by
  have hcf := continuous_fourier_lift hf1
  refine ⟨((continuous_sobolevWeight s).mul (hcf.norm.pow 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ξ =>
    mul_nonneg (sobolevWeight_nonneg s ξ) (by positivity))]
  rwa [sobolevNormSq_eq_lintegral_weight] at hfin

/-- **The `H^s`–`H^{−s}` duality bound in real form**, for real `f, g ∈ L¹ ∩ L²` with finite
Sobolev norms.  The two `toReal` conversions are legitimate: both norms are finite, and the
weighted Fourier moduli are integrable (`integrable_sobolevWeight_mul_norm_sq`). -/
theorem sq_abs_integral_mul_le_integral_weight {d : ℕ} (s : ℝ) {f g : Space d → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hf1 : Integrable f) (hg1 : Integrable g)
    (hfin : sobolevNormSq d s f < ⊤) (hgfin : sobolevNormSq d (-s) g < ⊤) :
    |∫ x, f x * g x| ^ 2
      ≤ (∫ ξ, sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2)
        * ∫ ξ, sobolevWeight (-s) ξ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖ ^ 2 := by
  rw [← sobolevNormSq_toReal_eq_integral s (integrable_sobolevWeight_mul_norm_sq s hf1 hfin),
    ← sobolevNormSq_toReal_eq_integral (-s)
      (integrable_sobolevWeight_mul_norm_sq (-s) hg1 hgfin),
    ← ENNReal.toReal_mul]
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hfin.ne hgfin.ne)).1
    (sobolevDualityBound_of_memLp s hf hg hf1 hg1)

end LatticeProb.Sobolev
