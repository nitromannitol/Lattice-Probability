import LatticeProb.Prob.MarkovPathKernelStrong

/-!
# Two-time laws of continuous Markov path kernels

The one-time transition laws of continuous Markov path kernels determine their
expectations against products of bounded continuous tests at two times.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- Equal one-time transition laws determine two-time product-test expectations. -/
theorem integral_eval_mul_eval_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (z : E) (s u : ℝ≥0) (f g : E →ᵇ ℝ) :
    ∫ x, f (x s) * g (x (s + u)) ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, f (x s) * g (x (s + u)) ∂(L z : Measure C(ℝ≥0, E)) := by
  let F : C(ℝ≥0, E) × C(ℝ≥0, E) → ℝ := fun p => f (p.1 s) * g (p.2 u)
  have hFm : Measurable F := by
    exact (f.continuous.measurable.comp ((continuous_eval_const s).measurable.comp measurable_fst)).mul
      (g.continuous.measurable.comp ((continuous_eval_const u).measurable.comp measurable_snd))
  have hFb : ∀ p, ‖F p‖ ≤ ‖f‖ * ‖g‖ := by
    intro p
    exact (norm_mul _ _).le.trans (mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _)
      (norm_nonneg _) (norm_nonneg _))
  have hk := (hMK z s).integral_eq_of_measurable hK hFm hFb
  have hl := (hML z s).integral_eq_of_measurable hL hFm hFb
  let H : E → ℝ := fun y => ∫ w, g (w u) ∂(K y : Measure C(ℝ≥0, E))
  have hH : Continuous H := by
    apply continuous_integral_of_continuous_measure hK
      (G := fun p : C(ℝ≥0, E) × E => g (p.1 u))
      (g.continuous.comp ((continuous_eval_const u).comp continuous_fst)) (C := ‖g‖)
    intro p
    exact g.norm_coe_le_norm _
  have hinner : ∀ y, H y = ∫ w, g (w u) ∂(L y : Measure C(ℝ≥0, E)) := by
    intro y
    have he := hmarg y u
    have hm := (continuous_eval_const u : Continuous fun x : C(ℝ≥0, E) => x u).measurable
    calc
      H y = ∫ v, g v ∂((K y : Measure C(ℝ≥0, E)).map (fun x => x u)) :=
        (integral_map hm.aemeasurable g.continuous.aestronglyMeasurable).symm
      _ = ∫ v, g v ∂((L y : Measure C(ℝ≥0, E)).map (fun x => x u)) := by rw [he]
      _ = _ := integral_map hm.aemeasurable g.continuous.aestronglyMeasurable
  have hout : (∫ x, f (x s) * H (x s) ∂(K z : Measure C(ℝ≥0, E))) =
      ∫ x, f (x s) * H (x s) ∂(L z : Measure C(ℝ≥0, E)) := by
    have he := hmarg z s
    have hm := (continuous_eval_const s : Continuous fun x : C(ℝ≥0, E) => x s).measurable
    have hf : Continuous (fun y => f y * H y) := f.continuous.mul hH
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
      ← integral_map hm.aemeasurable hf.aestronglyMeasurable, he]
  simp only [F, stopPath_apply, min_self, pathShift_apply, integral_const_mul] at hk hl
  rw [hk, hl]
  simpa only [← hinner] using hout

end LatticeProb
