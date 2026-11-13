/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.GaussianSq at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential moments of the square of a centred Gaussian

The Gaussian computation behind [18] = Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps*
(arXiv 1807.07511v3), Lemma A.4 : "the random variable
`𝔥(z) − 𝔥(0)` is centered Gaussian with variance `−log(1 − |z|²)` … Hence for a small enough universal choice of
`a₀ > 0`, `E[δ^{-2} ∫_{B_{2δ}(0)} exp(4πa₀ δ^{-2} (𝔥(z) − 𝔥(0))²) dz] ≲ 1`" , and of (A.9) in the proof of
Lemma A.5.

* `GMSAppA.integral_exp_mul_sq_gaussianReal`: for `X ∼ N(0, v)`, `v > 0`, and `2tv < 1`,
  `E[exp(t X²)] = (1 − 2tv)^{-1/2}`.
* `GMSAppA.integral_exp_mul_sq_gaussianReal_le`: the same bounded by `√2` when `4tv ≤ 1`, uniformly for `v = 0`.
* `GMSAppA.integrable_exp_mul_sq_gaussianReal`: integrability when `2tv < 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MatedCRTHarmonic.GMSAppA

/-- The Gaussian density times `exp(t x²)` is a Gaussian kernel with the reduced rate `1/(2v) − t`. -/
lemma gaussianPDFReal_zero_mul_exp_mul_sq (v : ℝ≥0) (t x : ℝ) :
    gaussianPDFReal 0 v x * rexp (t * x ^ 2) =
      (√(2 * π * v))⁻¹ * rexp (-((2 * (v : ℝ))⁻¹ - t) * x ^ 2) := by
  rw [gaussianPDFReal_def, mul_assoc, ← Real.exp_add]
  congr 2
  rw [sub_zero, neg_div, div_eq_mul_inv]
  ring
/-- The reduced Gaussian rate `1/(2v) − t = (1 − 2tv)/(2v)` is positive when `2tv < 1`. -/
lemma rate_pos {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 2 * t * v < 1) : 0 < (2 * (v : ℝ))⁻¹ - t := by
  have hvpos : (0 : ℝ) < v := by positivity
  have h1 : (2 * (v : ℝ))⁻¹ - t = (1 - 2 * t * v) / (2 * v) := by
    field_simp
  rw [h1]
  exact div_pos (by linarith) (by positivity)

/-- `exp(t x²)` is integrable against `N(0, v)` when `2tv < 1`. -/
lemma integrable_exp_mul_sq_gaussianReal {v : ℝ≥0} {t : ℝ} (ht : 2 * t * v < 1) :
    Integrable (fun x : ℝ => rexp (t * x ^ 2)) (gaussianReal 0 v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    exact integrable_dirac enorm_lt_top
  rw [gaussianReal_of_var_ne_zero _ hv]
  have hb := rate_pos hv ht
  rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
    (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have : (fun x : ℝ => rexp (t * x ^ 2) * (gaussianPDF 0 v x).toReal) =
      fun x => (√(2 * π * v))⁻¹ * rexp (-((2 * (v : ℝ))⁻¹ - t) * x ^ 2) := by
    funext x
    rw [toReal_gaussianPDF, mul_comm, gaussianPDFReal_zero_mul_exp_mul_sq]
  rw [this]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- **Exponential square moment of a centred Gaussian**: for `X ∼ N(0, v)` with `v > 0` and `2tv < 1`,
`E[exp(t X²)] = (1 − 2tv)^{-1/2}`. -/
theorem integral_exp_mul_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 2 * t * v < 1) :
    ∫ x, rexp (t * x ^ 2) ∂(gaussianReal 0 v) = (√(1 - 2 * t * v))⁻¹ := by
  have hvpos : (0 : ℝ) < v := by positivity
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, gaussianPDFReal_zero_mul_exp_mul_sq]
  rw [integral_const_mul, integral_gaussian]
  have h1 : (2 * (v : ℝ))⁻¹ - t = (1 - 2 * t * v) / (2 * v) := by
    field_simp
  have hpos : 0 < 1 - 2 * t * v := by linarith
  rw [h1, div_div_eq_mul_div, ← Real.sqrt_inv]
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  field_simp

/-- A uniform bound: `E[exp(t X²)] ≤ √2` for `X ∼ N(0, v)` whenever `4tv ≤ 1` (including `v = 0`). -/
theorem integral_exp_mul_sq_gaussianReal_le {v : ℝ≥0} {t : ℝ} (ht : 4 * t * v ≤ 1) :
    ∫ x, rexp (t * x ^ 2) ∂(gaussianReal 0 v) ≤ √2 := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, integral_dirac]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have ht' : 2 * t * v < 1 := by
    have : (0 : ℝ) < v := by positivity
    nlinarith
  rw [integral_exp_mul_sq_gaussianReal hv ht']
  have h12 : (1 : ℝ) / 2 ≤ 1 - 2 * t * v := by linarith
  calc (√(1 - 2 * t * v))⁻¹ ≤ (√(1 / 2))⁻¹ := by
        gcongr
    _ = √2 := by
        rw [one_div, Real.sqrt_inv, inv_inv]

end MatedCRTHarmonic.GMSAppA
