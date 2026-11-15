import LatticeProb.MeasureTheory.BoundedProfileIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Continuity of bounded density measures -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- Integrated truncated control of bounded nonnegative densities gives uniform Lipschitz
control of their measure evaluations. -/
theorem lipschitzWith_density_evaluation
    {Θ X : Type*} [PseudoMetricSpace Θ] [MeasurableSpace X] (μ : Measure X)
    (f : Θ → X → ℝ) (d : Θ → Θ → X → ℝ) (L : ℝ)
    (hf : ∀ θ, Integrable (f θ) μ)
    (hbound : ∀ θ, ∀ᵐ x ∂μ, 0 ≤ f θ x ∧ f θ x ≤ L)
    (hd : ∀ θ η, Integrable (fun x => min 1 (d θ η x)) μ)
    (hpoint : ∀ θ η, ∀ᵐ x ∂μ, |f θ x - f η x| ≤ d θ η x)
    (hcontrol : ∀ θ η, ∫ x, min 1 (d θ η x) ∂μ ≤ dist θ η)
    (s : Set X) (hs : MeasurableSet s) :
    LipschitzWith ⟨max 1 L, le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)⟩
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
    _ ≤ max 1 L * dist θ η :=
      mul_le_mul_of_nonneg_left (hcontrol θ η)
        (le_trans (by norm_num) (le_max_left _ _))

end LatticeProb
