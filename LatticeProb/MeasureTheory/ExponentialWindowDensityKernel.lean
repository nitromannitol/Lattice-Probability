import LatticeProb.MeasureTheory.ExponentialWindowIntegral
import LatticeProb.MeasureTheory.ScaledDensityFiniteKernel

/-! # Finite-window density kernels from exponentially weighted control -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Weighted half-line control of truncated discrepancies yields a finite kernel
of bounded densities on every finite time window. -/
theorem exists_finite_kernel_of_exponential_discrepancy_control
    {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (T L C : ℝ) (hC : 0 ≤ C) (f : Θ → ℝ → ℝ) (d : Θ → Θ → ℝ → ℝ)
    (hf : ∀ θ, Integrable (f θ) (volume.restrict (Ioo 0 T)))
    (hbound : ∀ θ, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ f θ t ∧ f θ t ≤ L)
    (hd : ∀ θ η, Integrable (fun t => min 1 (d θ η t)) (volume.restrict (Ioo 0 T)))
    (hw : ∀ θ η, Integrable (fun t => Real.exp (-t) * min 1 (d θ η t))
      (volume.restrict (Ioi 0)))
    (hnonneg : ∀ θ η, ∀ᵐ t ∂(volume.restrict (Ioi 0)), 0 ≤ d θ η t)
    (hpoint : ∀ θ η, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      |f θ t - f η t| ≤ d θ η t)
    (hcontrol : ∀ θ η, ∫ t in Ioi 0, Real.exp (-t) * min 1 (d θ η t)
      ≤ C * dist θ η) :
    ∃ κ : Kernel Θ ℝ, IsFiniteKernel κ ∧ ∀ θ,
      κ θ = (volume.restrict (Ioo 0 T)).withDensity (fun t => ENNReal.ofReal (f θ t)) := by
  apply exists_finite_kernel_of_bounded_density_scaled_control
    (volume.restrict (Ioo 0 T)) ?_ f d L (Real.exp T * C)
    (mul_nonneg (Real.exp_pos T).le hC) hf hbound hd hpoint
  · intro θ η
    calc
      ∫ t in Ioo 0 T, min 1 (d θ η t) ≤
          Real.exp T * ∫ t in Ioi 0, Real.exp (-t) * min 1 (d θ η t) :=
        integral_Ioo_le_exp_mul_integral_Ioi_exp_neg_mul T _ (hd θ η) (hw θ η)
          ((hnonneg θ η).mono fun _ ht => le_min (by norm_num) ht)
      _ ≤ (Real.exp T * C) * dist θ η := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcontrol θ η) (Real.exp_pos T).le
  · simp [Measure.restrict_apply, Real.volume_Ioo]

end LatticeProb
