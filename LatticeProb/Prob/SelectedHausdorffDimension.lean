import LatticeProb.Prob.ExpectedHausdorffCover
import LatticeProb.Prob.SelectedHausdorffCover

/-!
# Hausdorff dimension from selected covers

Finite families of deterministic sets selected by measurable events give an
almost-sure dimension bound when their expected costs are uniformly bounded.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LatticeProb

open Classical in
/-- A uniform first-moment bound for selected finite covers bounds dimension
almost surely on the event where the covers eventually contain the set. -/
theorem ae_dimH_le_of_selected_finite_cover
    {Ω X : Type*} [MeasurableSpace Ω] [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure Ω}
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ℝ≥0) (hd : 0 < d) (S : Ω → Set X) (A : Set Ω)
    (C : ∀ n, ι n → Set X) (E : ∀ n, ι n → Set Ω)
    (hE : ∀ n i, MeasurableSet (E n i)) (r : ℕ → ℝ≥0∞)
    (hr : Tendsto r atTop (𝓝 0))
    (hdiam : ∀ n i, Metric.ediam (C n i) ≤ r n)
    (hcover : ∀ ω ∈ A, ∀ᶠ n in atTop,
      S ω ⊆ ⋃ i, if ω ∈ E n i then C n i else ∅)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hcost : ∀ n, (∑ i, Metric.ediam (C n i) ^ (d : ℝ) * μ (E n i)) ≤ K) :
    ∀ᵐ ω ∂μ, ω ∈ A → dimH (S ω) ≤ (d : ℝ≥0∞) := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply ae_dimH_le_of_expected_finite_cover d S A
    (fun n i ω => if ω ∈ E n i then C n i else ∅) r hr
  · intro n i ω
    split_ifs
    · exact hdiam n i
    · simp only [Metric.ediam_empty, zero_le]
  · exact hcover
  · intro n
    exact (measurable_sum_selected_ediam_rpow (d : ℝ) hd' (C n) (E n) (hE n)).aemeasurable
  · exact hK
  · intro n
    rw [lintegral_sum_selected_ediam_rpow μ (d : ℝ) hd' (C n) (E n) (hE n)]
    exact hcost n

end LatticeProb
