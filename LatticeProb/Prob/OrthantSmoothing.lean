/-
# The orthant smoothing kernel: the Gaussian-smoothed orthant indicator (mvbe C1)

Route C1 needs the orthant smoothing kernel.  Unlike the one-dimensional `∏ sin(t_j)/t_j`, an
orthant of `ℝ^m` is not an integrable difference of boxes when `m > 1`, so the smoothing must be a
**Gaussian-smoothed orthant indicator**.  This module lands that kernel and its elementary facts:

* `orthantIndicator` — the indicator `1_{orthant h}`, nonnegative and at most `1`;
* `gaussDensityVec` — the (unnormalised) Gaussian smoothing density `z ↦ exp (-‖z‖² / (2 σ²))`;
* `orthantSmooth` — the smoothed orthant indicator: the `N(0, σ² I)`-mass of the orthant `≤ h`
  shifted by `-y`, i.e. the convolution of `orthantIndicator h` with the Gaussian kernel, together
  with its identification with `orthantProb` at the Gaussian covariance.

These are the objects the C1 smoothing inequality convolves with.  The remaining analytic input is
the Fourier transform of `orthantSmooth` — a product of smoothed half-line transforms.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityScalar
import LatticeProb.Prob.MultivariateSmoothing

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- **The orthant indicator** `1_{orthant h}`. -/
noncomputable def orthantIndicator {m : ℕ} (h : Fin m → ℝ) : (Fin m → ℝ) → ℝ :=
  (orthantSet h).indicator fun _ => 1

/-- The orthant indicator is nonnegative. -/
theorem orthantIndicator_nonneg {m : ℕ} (h : Fin m → ℝ) (y : Fin m → ℝ) :
    0 ≤ orthantIndicator h y :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) y

/-- The orthant indicator is at most `1`. -/
theorem orthantIndicator_le_one {m : ℕ} (h : Fin m → ℝ) (y : Fin m → ℝ) :
    orthantIndicator h y ≤ 1 := by
  rw [orthantIndicator]
  by_cases hy : y ∈ orthantSet h
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    exact zero_le_one

/-- The orthant indicator takes the value `1` on the orthant. -/
theorem orthantIndicator_of_mem {m : ℕ} {h : Fin m → ℝ} {y : Fin m → ℝ}
    (hy : y ∈ orthantSet h) : orthantIndicator h y = 1 :=
  Set.indicator_of_mem hy _

/-- The orthant indicator vanishes off the orthant. -/
theorem orthantIndicator_of_notMem {m : ℕ} {h : Fin m → ℝ} {y : Fin m → ℝ}
    (hy : y ∉ orthantSet h) : orthantIndicator h y = 0 :=
  Set.indicator_of_notMem hy _

/-- **The Gaussian smoothing density** (unnormalised) `z ↦ exp (-‖z‖² / (2 σ²))`. -/
noncomputable def gaussDensityVec {m : ℕ} (σ : ℝ) (z : Fin m → ℝ) : ℝ :=
  Real.exp (-(∑ j, z j ^ 2) / (2 * σ ^ 2))

/-- The Gaussian smoothing density is positive. -/
theorem gaussDensityVec_pos {m : ℕ} (σ : ℝ) (z : Fin m → ℝ) : 0 < gaussDensityVec σ z :=
  Real.exp_pos _

/-- **The Gaussian-smoothed orthant indicator**: the `N(0, σ² I)`-mass of the orthant `≤ h` shifted
by `-y`, i.e. the convolution of `orthantIndicator h` with the Gaussian kernel. -/
noncomputable def orthantSmooth {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) (y : Fin m → ℝ) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (σ ^ 2 • 1)
    {z : EuclideanSpace ℝ (Fin m) | ∀ j, y j + z j ≤ h j}).toReal

/-- The smoothed orthant indicator is nonnegative. -/
theorem orthantSmooth_nonneg {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) (y : Fin m → ℝ) :
    0 ≤ orthantSmooth h σ y :=
  ENNReal.toReal_nonneg

/-- The smoothed orthant indicator is at most `1` (it is a Gaussian mass of a set). -/
theorem orthantSmooth_le_one {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) (y : Fin m → ℝ) :
    orthantSmooth h σ y ≤ 1 := by
  rw [orthantSmooth]
  refine ENNReal.toReal_mono ENNReal.one_ne_top ?_
  calc multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (σ ^ 2 • 1)
        {z : EuclideanSpace ℝ (Fin m) | ∀ j, y j + z j ≤ h j}
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (σ ^ 2 • 1) Set.univ :=
        measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-- **The smoothed orthant indicator is monotone in the threshold**: a larger orthant has larger
Gaussian mass. -/
theorem orthantSmooth_mono {m : ℕ} {h h' : Fin m → ℝ} (hh : h ≤ h') (σ : ℝ) (y : Fin m → ℝ) :
    orthantSmooth h σ y ≤ orthantSmooth h' σ y := by
  rw [orthantSmooth, orthantSmooth]
  refine ENNReal.toReal_mono ?_ (measure_mono fun z hz j => le_trans (hz j) (hh j))
  exact ne_top_of_le_ne_top (by rw [measure_univ]; simp) (measure_mono (Set.subset_univ _))

/-- The smoothed orthant indicator lies in `[0, 1]`. -/
theorem orthantSmooth_mem_Icc {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) (y : Fin m → ℝ) :
    orthantSmooth h σ y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨orthantSmooth_nonneg h σ y, orthantSmooth_le_one h σ y⟩

/-- **The Gaussian-orthant comparison.**  The smoothed orthant indicator at the shift `y` is the
`N(0, σ² I)`-orthant mass of the threshold `h - y`: the Gaussian kernel spreads each point of the
orthant `≤ h` to the shifted orthant `≤ h - y`. -/
theorem orthantSmooth_eq_gaussianOrthant {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) (y : Fin m → ℝ) :
    orthantSmooth h σ y
      = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (σ ^ 2 • 1)
          {z : EuclideanSpace ℝ (Fin m) | ∀ j, z j ≤ (h - y) j}).toReal := by
  have hset : {z : EuclideanSpace ℝ (Fin m) | ∀ j, y j + z j ≤ h j}
      = {z : EuclideanSpace ℝ (Fin m) | ∀ j, z j ≤ (h - y) j} := by
    ext z
    simp only [Set.mem_setOf_eq, Pi.sub_apply]
    constructor <;> intro hz j <;> linarith [hz j]
  rw [orthantSmooth, hset]

/-- **The smoothed orthant indicator is antitone in the shift**: shifting the orthant further from
the origin can only lower the Gaussian mass. -/
theorem orthantSmooth_antitone_shift {m : ℕ} {y y' : Fin m → ℝ} (hy : y ≤ y') (h : Fin m → ℝ)
    (σ : ℝ) : orthantSmooth h σ y' ≤ orthantSmooth h σ y := by
  rw [orthantSmooth, orthantSmooth]
  refine ENNReal.toReal_mono ?_ (measure_mono fun z hz j => by have := hz j; have := hy j; linarith)
  exact ne_top_of_le_ne_top (by rw [measure_univ]; simp) (measure_mono (Set.subset_univ _))

/-- **The one-dimensional Fourier factor of the Gaussian smoothing kernel**: the Gaussian damping
`u ↦ exp (-(σ² u²) / 2)` that multiplies the transform of a one-dimensional half-line kernel. -/
noncomputable def gaussFourier1 (σ u : ℝ) : ℝ := Real.exp (-(σ ^ 2 * u ^ 2) / 2)

/-- **The Fourier factor of the Gaussian-smoothed orthant kernel.**  The smoothing kernel is a
product `∏ j g_σ (z j)`, so its Fourier factor is the product `∏ j, exp (-(σ² t j²) / 2)` of the
one-dimensional Gaussian factors.  This is the factor weighting the Sazonov remainder in the C1
smoothing inequality. -/
noncomputable def orthantFourierFactor {m : ℕ} (σ : ℝ) (t : Fin m → ℝ) : ℝ :=
  ∏ j, gaussFourier1 σ (t j)

/-- The one-dimensional Fourier factor is positive. -/
theorem gaussFourier1_pos (σ u : ℝ) : 0 < gaussFourier1 σ u := Real.exp_pos _

/-- The one-dimensional Fourier factor is `1` at the origin. -/
theorem gaussFourier1_zero (σ : ℝ) : gaussFourier1 σ 0 = 1 := by simp [gaussFourier1]

/-- The one-dimensional Fourier factor is at most `1`. -/
theorem gaussFourier1_le_one (σ u : ℝ) : gaussFourier1 σ u ≤ 1 := by
  rw [gaussFourier1, Real.exp_le_one_iff]
  nlinarith [sq_nonneg σ, sq_nonneg u]

/-- The Fourier factor is positive. -/
theorem orthantFourierFactor_pos {m : ℕ} (σ : ℝ) (t : Fin m → ℝ) :
    0 < orthantFourierFactor σ t :=
  Finset.prod_pos fun j _ => gaussFourier1_pos σ (t j)

/-- The Fourier factor is `1` at the origin. -/
theorem orthantFourierFactor_zero {m : ℕ} (σ : ℝ) :
    orthantFourierFactor σ (0 : Fin m → ℝ) = 1 := by
  simp [orthantFourierFactor, gaussFourier1]

/-- The Fourier factor is at most `1`. -/
theorem orthantFourierFactor_le_one {m : ℕ} (σ : ℝ) (t : Fin m → ℝ) :
    orthantFourierFactor σ t ≤ 1 :=
  Finset.prod_le_one (fun j _ => (gaussFourier1_pos σ (t j)).le)
    (fun j _ => gaussFourier1_le_one σ (t j))

/-- **The one-dimensional smoothed half-line kernel**: `x ↦ N(0, v)(Iic (c - x))`, the `v`-smoothed
indicator of the half-line `(-∞, c]`.  These are the one-dimensional factors of `orthantSmooth`,
so their Fourier transforms multiply `orthantFourierFactor`. -/
noncomputable def halfLineSmooth (c : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianReal 0 v (Set.Iic (c - x))).toReal

/-- The one-dimensional half-line kernel lies in `[0, 1]`. -/
theorem halfLineSmooth_mem_Icc (c : ℝ) (v : ℝ≥0) (x : ℝ) :
    halfLineSmooth c v x ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : gaussianReal 0 v (Set.Iic (c - x)) ≤ 1 := by
    calc gaussianReal 0 v (Set.Iic (c - x)) ≤ gaussianReal 0 v Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ⟨ENNReal.toReal_nonneg,
    (ENNReal.toReal_mono ENNReal.one_ne_top hle).trans_eq ENNReal.toReal_one⟩

/-- The one-dimensional half-line kernel is monotone in the half-line threshold. -/
theorem halfLineSmooth_mono_c {c c' : ℝ} (hc : c ≤ c') (v : ℝ≥0) (x : ℝ) :
    halfLineSmooth c v x ≤ halfLineSmooth c' v x := by
  refine ENNReal.toReal_mono ?_ (measure_mono fun z hz => ?_)
  · exact ne_top_of_le_ne_top (by rw [measure_univ]; simp) (measure_mono (Set.subset_univ _))
  · simp only [Set.mem_Iic] at hz ⊢
    linarith

/-- The one-dimensional half-line kernel is antitone in the shift. -/
theorem halfLineSmooth_antitone_x {x x' : ℝ} (hx : x ≤ x') (c : ℝ) (v : ℝ≥0) :
    halfLineSmooth c v x' ≤ halfLineSmooth c v x := by
  refine ENNReal.toReal_mono ?_ (measure_mono fun z hz => ?_)
  · exact ne_top_of_le_ne_top (by rw [measure_univ]; simp) (measure_mono (Set.subset_univ _))
  · simp only [Set.mem_Iic] at hz ⊢
    linarith

/-- **The product factorization of the orthant smoothing kernel.**  The Gaussian-smoothed orthant
indicator is the product of the one-dimensional smoothed half-line kernels: the kernel factors over
the coordinates, so its Fourier transform is the product of the one-dimensional half-line
transforms times the Gaussian factor `orthantFourierFactor`. -/
theorem orthantSmooth_eq_prod {m : ℕ} (h : Fin m → ℝ) {σ : ℝ} (hσ : 0 < σ) (y : Fin m → ℝ) :
    orthantSmooth h σ y = ∏ j, halfLineSmooth (h j) (Real.toNNReal (σ ^ 2)) (y j) := by
  have hvv : (Real.toNNReal (σ ^ 2) : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  have hvpos : (0 : ℝ≥0) < Real.toNNReal (σ ^ 2) := Real.toNNReal_pos.mpr (pow_pos hσ 2)
  rw [orthantSmooth_eq_gaussianOrthant]
  conv_lhs => rw [← hvv]
  rw [show (∏ j, halfLineSmooth (h j) (Real.toNNReal (σ ^ 2)) (y j))
      = ∏ j, (gaussianReal 0 (Real.toNNReal (σ ^ 2)) (Set.Iic ((h - y) j))).toReal from
    Finset.prod_congr rfl fun j _ => by rw [halfLineSmooth, Pi.sub_apply]]
  exact multivariateGaussian_orthant_scalar hvpos (h - y)

/-- **The one-dimensional half-line density**: the (negated) derivative `ψ' = -gaussPDF(c - ·)` of
the smoothed half-line is the explicit shifted Gaussian density `x ↦ gaussianPDFReal 0 v (c - x)`.
Its characteristic function is `charFun_gaussianReal`, so it replaces the distribution-valued
transform of the half-line itself. -/
noncomputable def halfLineDensity (c : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  gaussianPDFReal 0 v (c - x)

/-- The half-line density is nonnegative. -/
theorem halfLineDensity_nonneg (c : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ halfLineDensity c v x :=
  gaussianPDFReal_nonneg 0 v (c - x)

/-- **The one-dimensional half-line Fourier factor**, via the derivative: the explicit transform
`t ↦ e^{i c t} e^{-v t² / 2}` of the shifted Gaussian density `halfLineDensity c v` (the Gaussian
damping `gaussFourier1` multiplied by the half-line shift phase).  This replaces the absent
distributional transform of the half-line. -/
noncomputable def halfLineFourierFactor (c : ℝ) (v : ℝ≥0) (t : ℝ) : ℂ :=
  Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) * Complex.exp (-((v : ℝ) * t ^ 2) / 2)

/-- The half-line Fourier factor is `1` at the origin. -/
theorem halfLineFourierFactor_zero (c : ℝ) (v : ℝ≥0) : halfLineFourierFactor c v 0 = 1 := by
  simp [halfLineFourierFactor]

/-- **The density–characteristic-function link** at mean `c`: the Gaussian transform
`∫ x, gaussianPDFReal c v x · e^{i t x} = e^{i t c - v t²/2}`, from `charFun_gaussianReal`. -/
theorem integral_gaussianPDFReal_smul_mul_exp (c : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) :
    ∫ x, gaussianPDFReal c v x • Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I) ∂volume
      = Complex.exp (((t * c : ℝ) : ℂ) * Complex.I - (v : ℂ) * (t : ℂ) ^ 2 / 2) := by
  rw [← integral_gaussianReal_eq_integral_smul (μ := c) (v := v)
    (f := fun x : ℝ => Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I)) hv]
  have hcf : (∫ x : ℝ, Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I) ∂gaussianReal c v)
      = charFun (gaussianReal c v) t := by
    rw [charFun_apply_real]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    congr 1
    ring
  rw [hcf, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- **The half-line Fourier identity.**  The half-line Fourier factor is the transform of the
shifted Gaussian density: `∫ x, halfLineDensity c v x · e^{i t x} = halfLineFourierFactor c v t`.
The density `gaussianPDFReal 0 v (c - ·)` is the Gaussian density with mean `c`, so this is the
density–`charFun` link of `charFun_gaussianReal`. -/
theorem halfLineFourierFactor_eq (c : ℝ) {v : ℝ≥0} (hv : 0 < v) (t : ℝ) :
    ∫ x, (halfLineDensity c v x : ℂ) * Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I) ∂volume
      = halfLineFourierFactor c v t := by
  have hpoint : ∀ x : ℝ, halfLineDensity c v x = gaussianPDFReal c v x := by
    intro x
    simp only [halfLineDensity, gaussianPDFReal, sub_zero]
    congr 2
    ring
  have hint : (fun x : ℝ => (halfLineDensity c v x : ℂ)
        * Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I))
      = fun x : ℝ => (gaussianPDFReal c v x : ℂ)
        * Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I) := by
    funext x
    rw [hpoint x]
  have hsm : (fun x : ℝ => (gaussianPDFReal c v x : ℂ)
        * Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I))
      = fun x : ℝ => gaussianPDFReal c v x
        • Complex.exp (((x : ℂ) * (t : ℂ)) * Complex.I) := by
    funext x
    rw [Complex.real_smul]
  rw [hint, hsm, integral_gaussianPDFReal_smul_mul_exp c v hv.ne' t, halfLineFourierFactor,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The one-dimensional Fourier factor at `σ = 0` is the constant `1` (no smoothing). -/
theorem gaussFourier1_zero_sigma (u : ℝ) : gaussFourier1 0 u = 1 := by
  simp [gaussFourier1]

/-- The orthant Fourier factor at `σ = 0` is the constant `1`. -/
theorem orthantFourierFactor_zero_sigma {m : ℕ} (t : Fin m → ℝ) :
    orthantFourierFactor (0 : ℝ) t = 1 := by
  simp [orthantFourierFactor, gaussFourier1]

/-- **The Sazonov remainder weighted by the orthant Fourier factor.**  The Fourier factor
`orthantFourierFactor σ` — the transform of the product Gaussian smoothing kernel, times the
one-dimensional half-line transforms — weights the ball integral of the characteristic-function
difference in the Sazonov smoothing inequality. -/
noncomputable def sazonovWeightedRemainder {m : ℕ} (σ : ℝ) (μ μ' : Measure (Fin m → ℝ))
    (T : ℝ) : ℝ :=
  ∫ t in {t : Fin m → ℝ | (∑ j, t j ^ 2) ≤ T ^ 2},
    ‖charFunVec μ t - charFunVec μ' t‖ * orthantFourierFactor σ t ∂volume

/-- The weighted Sazonov remainder is nonnegative. -/
theorem sazonovWeightedRemainder_nonneg {m : ℕ} (σ : ℝ) (μ μ' : Measure (Fin m → ℝ)) (T : ℝ) :
    0 ≤ sazonovWeightedRemainder σ μ μ' T := by
  rw [sazonovWeightedRemainder]
  exact integral_nonneg fun t => mul_nonneg (norm_nonneg _) (orthantFourierFactor_pos σ t).le

/-- With no smoothing (`σ = 0`) the weighted remainder is the unweighted Sazonov remainder. -/
theorem sazonovWeightedRemainder_zero_sigma {m : ℕ} (μ μ' : Measure (Fin m → ℝ)) (T : ℝ) :
    sazonovWeightedRemainder 0 μ μ' T = sazonovRemainder μ μ' T := by
  rw [sazonovWeightedRemainder, sazonovRemainder]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [orthantFourierFactor, gaussFourier1]

/-- **The Sazonov multivariate smoothing inequality, weighted by the orthant Fourier factor.**
The C1 smoothing inequality with the Sazonov remainder weighted by `orthantFourierFactor σ`: the
Fourier factor of the Gaussian-smoothed orthant kernel (the product of the one-dimensional
half-line transforms, `halfLineFourierFactor_eq`).  Stated as a named `Prop`; the analytic content
is the bandwidth-vs-`m` balance producing the `m^{1/4}` factor. -/
def mvbeSazonovSmoothing : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (δ σ T : ℝ) (μ μ' : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure μ'],
      0 < δ → 0 < σ → 0 < T →
      NearIsotropic (covMatrix μ) δ → NearIsotropic (covMatrix μ') δ →
      ∀ h : Fin m → ℝ,
        |orthantProb μ h - orthantProb μ' h|
          ≤ C * ((m : ℝ) ^ ((1 : ℝ) / 4) * (1 + δ⁻¹))
              * sazonovWeightedRemainder σ μ μ' T + sazonovTail m T

end LatticeProb
