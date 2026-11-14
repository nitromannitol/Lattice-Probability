import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# Prepending a position test to Markov path expectations

Equal one-time laws and equal expectations of a future path functional give equal
expectations after prepending a bounded continuous test of the present position.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- A Markov step prepends a position test to an equal future expectation. -/
theorem integral_eval_mul_shift_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (G : C(ℝ≥0, E) →ᵇ ℝ)
    (hG : ∀ y, ∫ w, G w ∂(K y : Measure C(ℝ≥0, E)) =
      ∫ w, G w ∂(L y : Measure C(ℝ≥0, E)))
    (z : E) (s : ℝ≥0) (f : E →ᵇ ℝ) :
    ∫ x, f (x s) * G (pathShift x s) ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, f (x s) * G (pathShift x s) ∂(L z : Measure C(ℝ≥0, E)) := by
  let F : C(ℝ≥0, E) × C(ℝ≥0, E) → ℝ := fun p => f (p.1 s) * G p.2
  have hFm : Measurable F := by
    exact (f.continuous.measurable.comp ((continuous_eval_const s).measurable.comp measurable_fst)).mul
      (G.continuous.measurable.comp measurable_snd)
  have hFb : ∀ p, ‖F p‖ ≤ ‖f‖ * ‖G‖ := by
    intro p
    exact (norm_mul _ _).le.trans (mul_le_mul (f.norm_coe_le_norm _) (G.norm_coe_le_norm _)
      (norm_nonneg _) (norm_nonneg _))
  have hk := (hMK z s).integral_eq_of_measurable hK hFm hFb
  have hl := (hML z s).integral_eq_of_measurable hL hFm hFb
  let H : E → ℝ := fun y => ∫ w, G w ∂(K y : Measure C(ℝ≥0, E))
  have hH : Continuous H := by
    apply continuous_integral_of_continuous_measure hK
      (G := fun p : C(ℝ≥0, E) × E => G p.1)
      (G.continuous.comp continuous_fst) (C := ‖G‖)
    intro p
    exact G.norm_coe_le_norm _
  have hout : (∫ x, f (x s) * H (x s) ∂(K z : Measure C(ℝ≥0, E))) =
      ∫ x, f (x s) * H (x s) ∂(L z : Measure C(ℝ≥0, E)) := by
    have hm := (continuous_eval_const s : Continuous fun x : C(ℝ≥0, E) => x s).measurable
    have hf : Continuous (fun y => f y * H y) := f.continuous.mul hH
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
      ← integral_map hm.aemeasurable hf.aestronglyMeasurable, hmarg z s]
  simp only [F, stopPath_apply, min_self, integral_const_mul] at hk hl
  rw [hk, hl]
  simpa only [H, ← hG] using hout

end LatticeProb
