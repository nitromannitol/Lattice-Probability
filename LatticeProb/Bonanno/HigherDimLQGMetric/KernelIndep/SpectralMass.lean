/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.SpectralMass at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.SpectralDefs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrability and mass of the spectral band density

The dimension condition is required because `bandSpec` uses natural subtraction `d - 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd IsLFPPKernel)

private def specIntegrand {d : ℕ} (κ : Rd d → ℝ) (p : ℝ × Rd d) : ℝ :=
  p.1 ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (p.1 • p.2)‖ ^ 2

private theorem continuous_specIntegrand {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) : Continuous (specIntegrand κ) := by
  unfold specIntegrand
  exact (continuous_fst.pow _).mul (((ki_continuous_fourier_kernel hκ).comp
    (continuous_fst.smul continuous_snd)).norm.pow 2)

private theorem specIntegrand_slice_integrable {d : ℕ} (_hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun η : Rd d => specIntegrand κ (t, η)) volume := by
  unfold specIntegrand
  change Integrable (fun η : Rd d => t ^ (d - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2) volume
  exact ((integrable_fourier_kernel_norm_sq hκ).comp_smul ht.ne').const_mul _

private theorem specIntegrand_slice_integral {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    ∫ η : Rd d, specIntegrand κ (t, η) = t⁻¹ := by
  have hp : t ^ d = t ^ (d - 1) * t := by
    calc t ^ d = t ^ (d - 1 + 1) := by rw [Nat.sub_add_cancel hd]
      _ = t ^ (d - 1) * t := by rw [pow_add, pow_one]
  have hp' : t ^ (d - 1) = t ^ d / t := (eq_div_iff ht.ne').2 hp.symm
  have hs := integral_fourier_kernel_scaled hκ ht
  rw [integral_const_mul] at hs
  unfold specIntegrand
  change (∫ η : Rd d, t ^ (d - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2) = t⁻¹
  rw [integral_const_mul, hp']
  calc t ^ d / t * ∫ η : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2
      = (t ^ d * ∫ η : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2) / t := by ring
    _ = t⁻¹ := by rw [hs]; ring

private theorem specIntegrand_slice_norm_integral {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    ∫ η : Rd d, ‖specIntegrand κ (t, η)‖ = t⁻¹ := by
  have heq : (fun η : Rd d => ‖specIntegrand κ (t, η)‖) =
      (fun η : Rd d => specIntegrand κ (t, η)) := by
    funext η
    rw [Real.norm_eq_abs, abs_of_nonneg]
    unfold specIntegrand
    exact mul_nonneg (pow_nonneg ht.le _) (sq_nonneg _)
  rw [heq]
  exact specIntegrand_slice_integral hd hκ ht

/-- The Fourier-side spectral integrand is integrable on a positive finite band. -/
theorem integrable_specIntegrand {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    Integrable (specIntegrand κ) ((volume.restrict (Ioo a b)).prod volume) := by
  have hc := continuous_specIntegrand hκ
  refine (integrable_prod_iff hc.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact specIntegrand_slice_integrable hd hκ (ha.trans_le ht.1.le)
  · have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Icc a b) :=
      ContinuousOn.inv₀ continuousOn_id fun t ht =>
        (ha.trans_le ht.1).ne'
    have hInv : Integrable (fun t : ℝ => t⁻¹) (volume.restrict (Ioo a b)) :=
      (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    apply hInv.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (specIntegrand_slice_norm_integral hd hκ (ha.trans_le ht.1.le)).symm

/-- The spatial spectral density is integrable. -/
theorem integrable_bandSpec {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (bandSpec κ a b) volume := by
  have h := (integrable_specIntegrand hd hκ ha hab).integral_prod_right
  change Integrable (fun η : Rd d => ∫ t in Ioo a b,
    t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2) volume
  simpa only [specIntegrand] using h

/-- The spectral density is measurable as a parameterized integral of a continuous function. -/
theorem measurable_bandSpec {d : ℕ} {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (a b : ℝ) : Measurable (bandSpec κ a b) := by
  have h := (continuous_specIntegrand hκ).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioo a b))
  have hs : StronglyMeasurable (bandSpec κ a b) := by
    change StronglyMeasurable (fun η : Rd d => ∫ t in Ioo a b,
      t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2)
    simpa only [specIntegrand] using h
  exact hs.measurable

end HigherDimLQGMetric
