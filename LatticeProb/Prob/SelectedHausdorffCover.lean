import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# First moment of selected Hausdorff covers

The cost of a finite family of deterministic sets selected by measurable
events is measurable, and its expectation is the sum of the costs weighted
by the measures of the selection events.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {Ω X ι : Type*} [MeasurableSpace Ω] [EMetricSpace X] [Fintype ι]

open Classical in
omit [MeasurableSpace Ω] in
/-- The cost of a selected deterministic set is an indicator of its cost. -/
theorem selected_ediam_rpow_eq_indicator (d : ℝ) (hd : 0 < d)
    (C : Set X) (E : Set Ω) (ω : Ω) :
    Metric.ediam (if ω ∈ E then C else ∅) ^ d =
      E.indicator (fun _ => Metric.ediam C ^ d) ω := by
  classical
  by_cases h : ω ∈ E
  · simp [h]
  · simp [h, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hd]

open Classical in
/-- The cost of a finite selected family is measurable. -/
theorem measurable_sum_selected_ediam_rpow (d : ℝ) (hd : 0 < d)
    (C : ι → Set X) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) :
    Measurable (fun ω => ∑ i, Metric.ediam (if ω ∈ E i then C i else ∅) ^ d) := by
  classical
  simp_rw [selected_ediam_rpow_eq_indicator d hd]
  exact Finset.measurable_fun_sum _ fun i _ => measurable_const.indicator (hE i)

open Classical in
/-- The expected cost of a finite selected family is the sum of the costs
multiplied by the measures of their selection events. -/
theorem lintegral_sum_selected_ediam_rpow (μ : Measure Ω) (d : ℝ) (hd : 0 < d)
    (C : ι → Set X) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) :
    (∫⁻ ω, ∑ i, Metric.ediam (if ω ∈ E i then C i else ∅) ^ d ∂μ) =
      ∑ i, Metric.ediam (C i) ^ d * μ (E i) := by
  classical
  simp_rw [selected_ediam_rpow_eq_indicator d hd]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hE i))]
  exact Finset.sum_congr rfl fun i _ => lintegral_indicator_const (hE i) _

end LatticeProb
