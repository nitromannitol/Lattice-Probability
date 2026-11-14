import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Expected costs of Hausdorff covers

A uniform bound on the expected cost of finite covers at vanishing scales
bounds the Hausdorff dimension almost surely on the event where they cover.
The random cover cost is assumed almost everywhere measurable.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Finite covers with bounded expected `d`-cost give a dimension bound on
any event where they eventually cover the random set. -/
theorem ae_dimH_le_of_expected_finite_cover
    {Ω X : Type*} [MeasurableSpace Ω] [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure Ω}
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ℝ≥0) (S : Ω → Set X) (A : Set Ω)
    (T : ∀ n, ι n → Ω → Set X) (r : ℕ → ℝ≥0∞)
    (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ n i ω, Metric.ediam (T n i ω) ≤ r n)
    (hcover : ∀ ω ∈ A, ∀ᶠ n in atTop, S ω ⊆ ⋃ i, T n i ω)
    (hmeas : ∀ n, AEMeasurable (fun ω => ∑ i, Metric.ediam (T n i ω) ^ (d : ℝ)) μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcost : ∀ n, (∫⁻ ω, ∑ i, Metric.ediam (T n i ω) ^ (d : ℝ) ∂μ) ≤ C) :
    ∀ᵐ ω ∂μ, ω ∈ A → dimH (S ω) ≤ (d : ℝ≥0∞) := by
  have hlim : (∫⁻ ω, liminf (fun n => ∑ i, Metric.ediam (T n i ω) ^ (d : ℝ)) atTop ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (le_trans (lintegral_liminf_le' hmeas)
      (liminf_le_of_frequently_le' (.of_forall hcost))) (lt_top_iff_ne_top.mpr hC)
  filter_upwards [ae_lt_top' (.liminf hmeas) hlim] with ω hω hA
  apply dimH_le_of_hausdorffMeasure_ne_top
  apply ne_of_lt
  exact lt_of_le_of_lt
    (Measure.hausdorffMeasure_le_liminf_sum (d : ℝ) (S ω) r hr
      (fun n i => T n i ω) (Eventually.of_forall fun n i => hdiam n i ω) (hcover ω hA)) hω

end LatticeProb
