import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Convergence from integrated truncated distances -/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LatticeProb

/-- Vanishing integrated truncated distances imply convergence in measure. -/
theorem tendstoInMeasure_of_lintegral_min_edist
    {α E ι : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
    {μ : Measure α} {l : Filter ι} (f : ι → α → E) (g : α → E)
    (hmeas : ∀ i, AEMeasurable (fun x => min 1 (edist (f i x) (g x))) μ)
    (h : Tendsto (fun i => ∫⁻ x, min 1 (edist (f i x) (g x)) ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  let a : ℝ≥0∞ := min 1 ε
  have ha : 0 < a := lt_min (by simp) hε
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) (min_le_left _ _)
  have hlim : Tendsto (fun i => (∫⁻ x, min 1 (edist (f i x) (g x)) ∂μ) / a) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ENNReal.Tendsto.mul_const h (Or.inr (ENNReal.inv_ne_top.mpr ha.ne'))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) ?_
  intro i
  calc
    μ {x | ε ≤ edist (f i x) (g x)} ≤
        μ {x | a ≤ min 1 (edist (f i x) (g x))} := by
      apply measure_mono
      intro x hx
      change ε ≤ edist (f i x) (g x) at hx
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans hx)
    _ ≤ (∫⁻ x, min 1 (edist (f i x) (g x)) ∂μ) / a :=
      meas_ge_le_lintegral_div (hmeas i) ha.ne' hatop

end LatticeProb
