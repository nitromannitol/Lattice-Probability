/-
# The Fourier transform of a dilation and the mollifier normalisation

The density input of the Rellich support repair (`MollifierFourierTendsto`, consumed by
`exists_testFn_approx_of_fourier_tendsto` in `SupportDensity.lean`) needs the standard
**scaling identity** for the Fourier transform of a rescaled function,

  `𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w)`  (`a > 0`),

whose `a → ∞` corollary `𝓕 f (· / a) → 𝓕 f 0 = ∫ f` is the pointwise
convergence of the
mollifier Fourier transforms.  Mathlib has the two ingredients but not the identity:
`MeasureTheory.Measure.integral_comp_smul_of_nonneg`
(`MeasureTheory/Measure/Haar/NormedSpace.lean`) does the substitution, and `Real.fourier_eq`
with `VectorFourier.fourierIntegral_continuous` gives the pointwise form and the continuity of
`𝓕 f`.  This file lands the identity, its companions, and the whole normalised-dilation
mollifier: `mollifierFourierTendsto` proves `MollifierFourierTendsto`, i.e.
`𝓕 χ_n → 1` pointwise and `‖𝓕 χ_n‖ ≤ 1` for `χ_n x = n^d • φ (n • x)`
with `∫ φ = 1`.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import LatticeProb.Analysis.Sobolev.SupportDensity

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The Fourier transform of a dilation.**  For `a > 0` and `f : Space d → ℂ`,
`𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w)`.  This is the
scaling identity the
mollifier argument needs; it is not in Mathlib. -/
theorem fourier_comp_smul {d : ℕ} (f : Space d → ℂ) {a : ℝ} (ha : 0 < a)
    (w : Space d) :
    𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hinner : ∀ v : Space d, inner ℝ (a • v) (a⁻¹ • w) = inner ℝ v w := by
    intro v
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ ha.ne',
      one_mul]
  have hsc := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume)
    (fun v : Space d => 𝐞 (-(inner ℝ v (a⁻¹ • w))) • f v) a (hR := ha.le)
  have hL : (∫ v, 𝐞 (-(inner ℝ (a • v) (a⁻¹ • w))) • f (a • v))
      = ∫ v, 𝐞 (-(inner ℝ v w)) • f (a • v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change 𝐞 (-(inner ℝ (a • v) (a⁻¹ • w))) • f (a • v)
      = 𝐞 (-(inner ℝ v w)) • f (a • v)
    rw [hinner v]
  rw [hL] at hsc
  rw [finrank_euclideanSpace, Fintype.card_fin] at hsc
  exact hsc

/-- **The Fourier transform at frequency zero is the integral.**  `𝓕 f 0 = ∫ f`. -/
theorem fourier_zero_eq_integral {d : ℕ} (f : Space d → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_eq]
  simp

/-- **The Fourier transform is continuous** for an integrable function. -/
theorem continuous_fourier {d : ℕ} {f : Space d → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ (Space d))
    Real.continuous_fourierChar continuous_inner hf

/-- **The constant-scalar rule for the Fourier transform.**  `𝓕 (c • f) = c • 𝓕 f`. -/
theorem fourier_const_smul {d : ℕ} (c : ℂ) (f : Space d → ℂ) :
    𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ (Space d)) f c

/-- **The normalised dilation has no scaling factor.**  For `χ_a x = a^d • f (a • x)`,
`𝓕 (χ_a) w = 𝓕 f (a⁻¹ • w)`: the `a^d` normalisation cancels the `(a^d)⁻¹` of
`fourier_comp_smul`. -/
theorem fourier_normalized_dilation {d : ℕ} (f : Space d → ℂ) {a : ℝ} (ha : 0 < a)
    (w : Space d) :
    𝓕 (fun x => ((a ^ d : ℝ) : ℂ) • f (a • x)) w = 𝓕 f (a⁻¹ • w) := by
  have hconst : 𝓕 (fun x => ((a ^ d : ℝ) : ℂ) • f (a • x)) w
      = ((a ^ d : ℝ) : ℂ) • 𝓕 (fun x => f (a • x)) w :=
    congrFun (fourier_const_smul ((a ^ d : ℝ) : ℂ) (fun x => f (a • x))) w
  rw [hconst, fourier_comp_smul f ha w]
  have hpow : (a ^ d : ℝ) ≠ 0 := pow_ne_zero d ha.ne'
  rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow, Complex.ofReal_one, one_mul]

/-- The normalised dilations of `φ`: `χ n x = (n + 1)^d • φ ((n + 1) • x)`.
Shifting the index by
one keeps the scale `n + 1` strictly positive, so no `0`-scale case arises. -/
noncomputable def mollifierDil (d : ℕ) (φ : Space d → ℂ) (n : ℕ) : Space d → ℂ :=
  fun x => ((((n : ℝ) + 1) ^ d : ℝ) : ℂ) • φ (((n : ℝ) + 1) • x)

/-- The Fourier transform of the normalised dilation is the Fourier transform of `φ` at the
rescaled frequency. -/
theorem fourier_mollifierDil {d : ℕ} (φ : Space d → ℂ) (n : ℕ) (ξ : Space d) :
    𝓕 (mollifierDil d φ n) ξ = 𝓕 φ (((n : ℝ) + 1)⁻¹ • ξ) :=
  fourier_normalized_dilation φ (by positivity) ξ

/-- The uniform bound `‖𝓕 χ_n‖ ≤ 1` for a normalised `φ`. -/
theorem norm_fourier_mollifierDil_le {d : ℕ} {φ : Space d → ℂ}
    (hnorm : ∫ x, ‖φ x‖ ≤ 1) (n : ℕ) (ξ : Space d) :
    ‖𝓕 (mollifierDil d φ n) ξ‖ ≤ 1 := by
  rw [fourier_mollifierDil φ n ξ]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ (Space d)) φ (((n : ℝ) + 1)⁻¹ • ξ)).trans hnorm

/-- **The mollifier Fourier transforms tend to `1`.**  For `φ` with `∫ φ = 1`,
`𝓕 χ_n ξ → 1` at every frequency. -/
theorem tendsto_fourier_mollifierDil {d : ℕ} {φ : Space d → ℂ} (hf : Integrable φ)
    (hint : ∫ x, φ x = 1) (ξ : Space d) :
    Tendsto (fun n : ℕ => 𝓕 (mollifierDil d φ n) ξ) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • ξ) atTop (𝓝 0) := by
    simpa using h1.smul_const ξ
  have h3 : Tendsto (fun n : ℕ => 𝓕 φ (((n : ℝ) + 1)⁻¹ • ξ)) atTop
      (𝓝 (𝓕 φ 0)) :=
    ((continuous_fourier hf).tendsto 0).comp h2
  rw [fourier_zero_eq_integral, hint] at h3
  exact Tendsto.congr'
    (Filter.Eventually.of_forall fun n => (fourier_mollifierDil φ n ξ).symm) h3

/-- **The mollifier Fourier-normalisation data.**  For a normalised bump `φ` (`∫ φ = 1`,
`∫ ‖φ‖ ≤ 1`), the normalised dilations `χ_n` satisfy `𝓕 χ_n → 1` pointwise and
`‖𝓕 χ_n‖ ≤ 1`.
This is the input `exists_testFn_approx_of_fourier_tendsto` (`SupportDensity.lean`) consumes. -/
def MollifierFourierTendsto (d : ℕ) (φ : Space d → ℂ) : Prop :=
  (∀ ξ : Space d, Tendsto (fun n : ℕ => 𝓕 (mollifierDil d φ n) ξ) atTop (𝓝 1)) ∧
  (∀ (n : ℕ) (ξ : Space d), ‖𝓕 (mollifierDil d φ n) ξ‖ ≤ 1)

/-- `MollifierFourierTendsto` holds for every normalised bump. -/
theorem mollifierFourierTendsto {d : ℕ} {φ : Space d → ℂ} (hf : Integrable φ)
    (hint : ∫ x, φ x = 1) (hnorm : ∫ x, ‖φ x‖ ≤ 1) :
    MollifierFourierTendsto d φ :=
  ⟨fun ξ => tendsto_fourier_mollifierDil hf hint ξ,
    fun n ξ => norm_fourier_mollifierDil_le hnorm n ξ⟩

/-- **Dominated convergence with a bounded Fourier factor.**  The general form of
`tendsto_sobolevNormSq_of_fourier_factor` (`TestFnApprox.lean`) where the factor is bounded by an
arbitrary `C ≥ 0` rather than `1`.  The convolution factor of the standard mollifier,
`c n = 1 - 𝓕 χ_n`, satisfies only `‖c n‖ ≤ 2` (since `‖𝓕 χ_n‖ ≤ 1`), so this is
the form the
density route needs. -/
theorem tendsto_sobolevNormSq_of_fourier_factor_le {d : ℕ} {s : ℝ} {u : Space d → ℝ}
    {w : ℕ → Space d → ℝ} {c : ℕ → Space d → ℂ} {C : ℝ}
    (hu : sobolevNormSq d s u < ⊤)
    (hid : ∀ n ξ, 𝓕 (fun x => (w n x : ℂ)) ξ = 𝓕 (fun x => (u x : ℂ)) ξ * c n ξ)
    (hF : ∀ n, AEMeasurable (fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2)) volume)
    (hbound : ∀ n ξ, ‖c n ξ‖ ≤ C)
    (hcv : ∀ ξ, Tendsto (fun n => c n ξ) atTop (𝓝 0)) :
    Tendsto (fun n => sobolevNormSq d s (w n)) atTop (𝓝 0) := by
  have key : (fun n => sobolevNormSq d s (w n))
      = fun n => ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2) := by
    funext n
    unfold sobolevNormSq
    refine lintegral_congr fun ξ => ?_
    rw [hid n ξ, norm_mul]
  rw [key]
  have hbound_eq : (∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2))
      = ENNReal.ofReal (C ^ 2) * sobolevNormSq d s u := by
    unfold sobolevNormSq
    rw [show (fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2))
        = fun ξ => ENNReal.ofReal (C ^ 2) *
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
            ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2) from by
      funext ξ
      have hCpow : (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2
          = C ^ 2 * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2 := mul_pow C _ 2
      rw [hCpow,
        show (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
            (C ^ 2 * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2)
            = C ^ 2 * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2) by ring,
        ENNReal.ofReal_mul (sq_nonneg C)]]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : (∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
      (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2)) ≠ ⊤ := by
    rw [hbound_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu.ne
  have hlim := tendsto_lintegral_of_dominated_convergence'
      (F := fun n ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2))
      (f := fun _ => (0 : ℝ≥0∞))
      (bound := fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖) ^ 2))
      hF (fun n => by
        filter_upwards with ξ
        apply ENNReal.ofReal_le_ofReal
        have hw : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := Real.rpow_nonneg (by positivity) s
        have h1 : ‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖
            ≤ C * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ := by
          rw [mul_comm C]
          exact mul_le_mul_of_nonneg_left (hbound n ξ)
            (norm_nonneg (𝓕 (fun x => (u x : ℂ)) ξ))
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h1 2) hw)
      hfin (by
        filter_upwards with ξ
        have h1 : Tendsto (fun n => ‖c n ξ‖) atTop (𝓝 0) :=
          by simpa using Filter.Tendsto.norm (hcv ξ)
        have h3 : Tendsto (fun n => ‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) atTop
            (𝓝 0) := by
          simpa using h1.const_mul (‖𝓕 (fun x => (u x : ℂ)) ξ‖)
        have h4 : Tendsto (fun n => (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2)
            atTop (𝓝 0) := by simpa using h3.pow 2
        have h5 : Tendsto (fun n => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
            (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2) atTop (𝓝 0) :=
          by simpa using h4.const_mul ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s)
        simpa only [Function.comp_def, ENNReal.ofReal_zero] using
          (ENNReal.continuous_ofReal.tendsto 0).comp h5)
  simpa using hlim

/-- **The density theorem with a bounded Fourier factor.**  The general form of
`exists_testFn_approx_of_fourier_tendsto` (`SupportDensity.lean`) with `‖c n‖ ≤ C`; it
composes
`tendsto_sobolevNormSq_of_fourier_factor_le` with the definition of convergence.  The standard
mollifier factor `c n = 1 - 𝓕 χ_n` has `C = 2`. -/
theorem exists_testFn_approx_of_fourier_tendsto_le {d : ℕ} {D : Set (Space d)}
    {u : Space d → ℝ} {s : ℝ} (hu : sobolevNormSq d s u < ⊤)
    (w : ℕ → Space d → ℝ) (hw : ∀ n, IsTestFn D (fun x => u x - w n x))
    (c : ℕ → Space d → ℂ) {C : ℝ}
    (hid : ∀ n ξ, 𝓕 (fun x => (w n x : ℂ)) ξ = 𝓕 (fun x => (u x : ℂ)) ξ * c n ξ)
    (hF : ∀ n, AEMeasurable (fun ξ => ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        (‖𝓕 (fun x => (u x : ℂ)) ξ‖ * ‖c n ξ‖) ^ 2)) volume)
    (hbound : ∀ n ξ, ‖c n ξ‖ ≤ C)
    (hcv : ∀ ξ, Tendsto (fun n => c n ξ) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ ψ : Space d → ℝ, IsTestFn D ψ ∧
      sobolevNormSq d s (fun x => u x - ψ x) ≤ ENNReal.ofReal η := by
  have ht := tendsto_sobolevNormSq_of_fourier_factor_le hu hid hF hbound hcv
  have hlt : ∀ᶠ n in atTop, sobolevNormSq d s (w n) < ENNReal.ofReal η :=
    (tendsto_order.1 ht).2 (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨n, hn⟩ := hlt.exists
  refine ⟨fun x => u x - w n x, hw n, ?_⟩
  have hfun : (fun x => u x - (fun x => u x - w n x) x) = w n := by funext x; ring
  rw [hfun]
  exact le_of_lt hn

end LatticeProb.Sobolev
