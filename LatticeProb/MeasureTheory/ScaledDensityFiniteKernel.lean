import LatticeProb.MeasureTheory.BoundedDensityFiniteKernel

/-! # Finite kernels with scaled density control -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

/-- A fixed multiple of the parameter distance controlling integrated truncated
profile discrepancies gives Lipschitz measure evaluations. -/
theorem lipschitzWith_density_evaluation_of_scaled_control
    {Θ X : Type*} [PseudoMetricSpace Θ] [MeasurableSpace X] (μ : Measure X)
    (f : Θ → X → ℝ) (d : Θ → Θ → X → ℝ) (L C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ θ, Integrable (f θ) μ)
    (hbound : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ f θ x ∧ f θ x ≤ L)
    (hd : ∀ θ η, Integrable (fun x => min 1 (d θ η x)) μ)
    (hpoint : ∀ θ η, ∀ᵐ x ∂μ, |f θ x - f η x| ≤ d θ η x)
    (hcontrol : ∀ θ η, ∫ x, min 1 (d θ η x) ∂μ ≤ C * dist θ η)
    (s : Set X) (hs : MeasurableSet s) :
    LipschitzWith ⟨max 1 L * C, mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) hC⟩
      (fun θ => (μ.withDensity (fun x => ENNReal.ofReal (f θ x)) s).toReal) := by
  have heval (θ : Θ) :
      (μ.withDensity (fun x => ENNReal.ofReal (f θ x)) s).toReal =
        ∫ x in s, f θ x ∂μ := by
    rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
      ((hf θ).mono_measure Measure.restrict_le_self)
      (ae_restrict_of_ae ((hbound θ).mono fun _ hx => hx.1)), ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae (ae_restrict_of_ae ((hbound θ).mono fun _ hx => hx.1))
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  rw [Real.dist_eq, heval θ, heval η]
  have hpoint' : ∀ᵐ x ∂μ, (0 ≤ f θ x ∧ f θ x ≤ L) ∧
      (0 ≤ f η x ∧ f η x ≤ L) ∧ |f θ x - f η x| ≤ d θ η x := by
    filter_upwards [hbound θ, hbound η, hpoint θ η] with x ha hb hc
    exact ⟨ha, hb, hc⟩
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ min 1 (d θ η x) := by
    filter_upwards [hpoint θ η] with x hx
    exact le_min (by norm_num) ((abs_nonneg _).trans hx)
  calc
    |∫ x in s, f θ x ∂μ - ∫ x in s, f η x ∂μ| ≤
        max 1 L * ∫ x in s, min 1 (d θ η x) ∂μ :=
      abs_setIntegral_sub_le_truncated_discrepancy (hf θ) (hf η) (hd θ η) hpoint' s
    _ ≤ max 1 L * ∫ x, min 1 (d θ η x) ∂μ :=
      mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self hnonneg (hd θ η))
        (le_trans (by norm_num) (le_max_left _ _))
    _ ≤ (max 1 L * C) * dist θ η := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcontrol θ η)
        (le_trans (by norm_num) (le_max_left _ _))

/-- Bounded densities with scaled integrated discrepancy control form a finite kernel. -/
theorem exists_finite_kernel_of_bounded_density_scaled_control
    {Θ X : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    [MeasurableSpace X] (μ : Measure X) (hμ : μ Set.univ < ∞)
    (f : Θ → X → ℝ) (d : Θ → Θ → X → ℝ) (L C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ θ, Integrable (f θ) μ)
    (hbound : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ f θ x ∧ f θ x ≤ L)
    (hd : ∀ θ η, Integrable (fun x => min 1 (d θ η x)) μ)
    (hpoint : ∀ θ η, ∀ᵐ x ∂μ, |f θ x - f η x| ≤ d θ η x)
    (hcontrol : ∀ θ η, ∫ x, min 1 (d θ η x) ∂μ ≤ C * dist θ η) :
    ∃ κ : Kernel Θ X, IsFiniteKernel κ ∧
      ∀ θ, κ θ = μ.withDensity (fun x => ENNReal.ofReal (f θ x)) := by
  apply exists_finite_kernel_of_continuous_measure_evaluations
    (fun θ => μ.withDensity (fun x => ENNReal.ofReal (f θ x)))
    (ENNReal.ofReal L * μ Set.univ)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ
  · intro θ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← lintegral_const]
    exact lintegral_mono_ae ((hbound θ).mono fun _ hx => ENNReal.ofReal_le_ofReal hx.2)
  · intro s hs
    exact (lipschitzWith_density_evaluation_of_scaled_control μ f d L C hC hf hbound hd
      hpoint hcontrol s hs).continuous

end LatticeProb
