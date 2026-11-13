/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.SpectralDefs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.Version
import LatticeProb.Bonanno.HigherDimLFPP.Field.Kernel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Spectral representatives of LFPP band fields

These are the Fourier-side densities and cosine-sine vectors in MA6 P15. The two disjoint
intervals in the first coordinate of white noise realize the real and imaginary phases.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN IsLFPPKernel)

/-- The complexification of an admissible real kernel is a Schwartz function. -/
def kiKernelSchwartz {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    SchwartzMap (Rd d) ℂ :=
  (hκ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hκ.contDiff)

@[simp] theorem kiKernelSchwartz_apply {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (x : Rd d) : kiKernelSchwartz hκ x = (κ x : ℂ) := rfl

/-- Plancherel and the normalization `∫ κ² = 1`. -/
theorem integral_fourier_kernel_norm_sq {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) :
    ∫ η : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) η‖ ^ 2 = 1 := by
  have h := SchwartzMap.integral_norm_sq_fourier (kiKernelSchwartz hκ)
  have hfun : (kiKernelSchwartz hκ : Rd d → ℂ) = fun x => (κ x : ℂ) := by
    funext x
    rfl
  simp only [hfun, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h.trans hκ.integral_sq

/-- The squared Fourier amplitude is integrable. -/
theorem integrable_fourier_kernel_norm_sq {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) :
    Integrable (fun η : Rd d => ‖𝓕 (fun x : Rd d => (κ x : ℂ)) η‖ ^ 2) volume := by
  have h := ((𝓕 (kiKernelSchwartz hκ)).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hfun : (kiKernelSchwartz hκ : Rd d → ℂ) = fun x => (κ x : ℂ) := by
    funext x
    rfl
  simpa only [SchwartzMap.fourier_coe, hfun] using h

/-- Fourier transforms of admissible kernels are continuous. -/
theorem ki_continuous_fourier_kernel {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) :
    Continuous (fun η : Rd d => 𝓕 (fun x : Rd d => (κ x : ℂ)) η) := by
  have hfun : (kiKernelSchwartz hκ : Rd d → ℂ) = fun x => (κ x : ℂ) := by
    funext x
    rfl
  simpa only [SchwartzMap.fourier_coe, hfun] using (𝓕 (kiKernelSchwartz hκ)).continuous

/-- Scaling preserves the normalized Fourier mass after inserting the Jacobian `t^d`. -/
theorem integral_fourier_kernel_scaled {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    ∫ η : Rd d, t ^ d * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2 = 1 := by
  have h := Measure.integral_comp_smul (volume : Measure (Rd d))
    (fun η : Rd d => ‖𝓕 (fun x : Rd d => (κ x : ℂ)) η‖ ^ 2) t
  rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ht _))] at h
  simp only [smul_eq_mul] at h
  rw [integral_fourier_kernel_norm_sq hκ] at h
  simp only [mul_one] at h
  rw [integral_const_mul]
  have ht0 : t ^ d ≠ 0 := ne_of_gt (pow_pos ht _)
  calc t ^ d * ∫ η : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2
      = t ^ d * (t ^ d)⁻¹ := by rw [h]
    _ = 1 := mul_inv_cancel₀ ht0

/-- The squared Fourier amplitude is radial, as required by the polar cancellation in KI-2. -/
theorem ki_fourier_kernel_eq_of_norm_eq {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {η η' : Rd d} (hη : ‖η‖ = ‖η'‖) :
    𝓕 (fun x : Rd d => (κ x : ℂ)) η =
      𝓕 (fun x : Rd d => (κ x : ℂ)) η' := by
  let A : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (η - η'))ᗮ.reflection
  have hA : A η = η' := Submodule.reflection_sub hη
  have hfun : (fun x : Rd d => (κ (A x) : ℂ)) = fun x => (κ x : ℂ) := by
    funext x
    rw [hκ.comp_linearIsometryEquiv A]
  have h := Real.fourier_comp_linearIsometry A (fun x : Rd d => (κ x : ℂ)) η
  change 𝓕 (fun x : Rd d => (κ (A x) : ℂ)) η = _ at h
  rw [hfun, hA] at h
  exact h

/-- Spectral density of the band from scale `a` to `b`. -/
def bandSpec {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ) (η : Rd d) : ℝ :=
  ∫ t in Ioo a b, t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2

/-- Spectral densities are nonnegative when the scale range is positive. -/
theorem bandSpec_nonneg {d : ℕ} (κ : Rd d → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (η : Rd d) : 0 ≤ bandSpec κ a b η := by
  unfold bandSpec
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact mul_nonneg (pow_nonneg (ha.trans ht.1.le) _) (sq_nonneg _)

/-- Real-valued cosine-sine realization of the spectral band vector. -/
def specFun {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ) (z : Rd d) (p : ℝ × Rd d) : ℝ :=
  (Ico (0 : ℝ) 1).indicator (fun _ => Real.sqrt (bandSpec κ a b p.2) *
      Real.cos (2 * Real.pi * inner ℝ z p.2)) p.1 +
    (Ico (1 : ℝ) 2).indicator (fun _ => Real.sqrt (bandSpec κ a b p.2) *
      Real.sin (2 * Real.pi * inner ℝ z p.2)) p.1

open Classical in
/-- Spectral vector, with the standard `Lp` totalization outside its integrable domain. -/
def specVec {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ) (z : Rd d) : WN d :=
  if h : MemLp (specFun κ a b z) 2 volume then h.toLp _ else 0

end HigherDimLQGMetric
