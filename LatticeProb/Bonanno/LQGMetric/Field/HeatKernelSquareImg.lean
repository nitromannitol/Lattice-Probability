/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareImg at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Structure of the image-series interval kernel (task P2-DDDFP29, WP-110)

Ingredients of the Chapman–Kolmogorov identity for the Dirichlet kernel of `(a, a+L)` by the
method of images (Feller, *An Introduction to Probability Theory and its Applications* II,
§X.5): the image series `q_s(·, v)` is `2L`-periodic and odd about `a` (so it vanishes at the
endpoints `a` and `a + L`), and the one-dimensional Gaussian kernels satisfy
`∫ g_s(u − w) g_r(w − v) dw = g_{s+r}(u − v)`.
-/

noncomputable section

open MeasureTheory Real

namespace LQGMetric
namespace HeatSq

/-- Completing the square in one dimension. -/
lemma gauss1_mul_gauss1_ck (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (u w v : ℝ) :
    gauss1 s (u - w) * gauss1 r (w - v) =
      ((Real.sqrt (2 * π * s))⁻¹ * (Real.sqrt (2 * π * r))⁻¹ *
        Real.exp (-(u - v) ^ 2 / (2 * (s + r)))) *
        Real.exp (-((s + r) / (2 * s * r)) * (w - (r / (s + r) * u + s / (s + r) * v)) ^ 2) := by
  have hsr : 0 < s + r := by positivity
  have key : -(u - w) ^ 2 / (2 * s) + -(w - v) ^ 2 / (2 * r) =
      -(u - v) ^ 2 / (2 * (s + r)) +
        -((s + r) / (2 * s * r)) * (w - (r / (s + r) * u + s / (s + r) * v)) ^ 2 := by
    field_simp
    ring
  unfold gauss1
  rw [mul_mul_mul_comm, ← Real.exp_add, key, Real.exp_add]
  ring

lemma integrable_gauss1_mul_gauss1 (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (u v : ℝ) :
    Integrable (fun w => gauss1 s (u - w) * gauss1 r (w - v)) := by
  have hb : 0 < (s + r) / (2 * s * r) := by positivity
  simp_rw [gauss1_mul_gauss1_ck s r hs hr u _ v]
  exact ((integrable_exp_neg_mul_sq hb).comp_sub_right _).const_mul _

/-- **One-dimensional Chapman–Kolmogorov**: `∫ g_s(u − w) g_r(w − v) dw = g_{s+r}(u − v)`. -/
theorem integral_gauss1_mul_gauss1 (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (u v : ℝ) :
    ∫ w, gauss1 s (u - w) * gauss1 r (w - v) = gauss1 (s + r) (u - v) := by
  have hsr : 0 < s + r := by positivity
  simp_rw [gauss1_mul_gauss1_ck s r hs hr u _ v]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun w : ℝ => Real.exp (-((s + r) / (2 * s * r)) * w ^ 2)), integral_gaussian]
  have hsq : (Real.sqrt (2 * π * s))⁻¹ * (Real.sqrt (2 * π * r))⁻¹ *
      Real.sqrt (π / ((s + r) / (2 * s * r))) = (Real.sqrt (2 * π * (s + r)))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv,
      ← Real.sqrt_mul (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * π * s)),
      ← Real.sqrt_mul (mul_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * π * s))
        (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * π * r)))]
    congr 1
    field_simp
  unfold gauss1
  rw [← hsq]
  ring

end HeatSq
end LQGMetric
