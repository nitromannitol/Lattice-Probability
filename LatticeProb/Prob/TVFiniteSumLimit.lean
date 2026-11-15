import LatticeProb.Prob.TVFiniteSum
import LatticeProb.Prob.TVScalar

/-! Convergence in total variation for finite weighted sums. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Finite weighted sums preserve convergence in total variation, for finite
weights and measures which may vary along an arbitrary filter. -/
theorem tendsto_tvDist_finset_sum_smul {α ι τ : Type*} [MeasurableSpace α]
    {l : Filter τ} (s : Finset ι) (c : ι → ℝ≥0∞)
    (hc : ∀ i ∈ s, c i ≠ ⊤) (μ ν : ι → τ → Measure α)
    (h : ∀ i ∈ s, Tendsto (fun t => QuantumZipper.TV.tvDist (μ i t) (ν i t)) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (∑ i ∈ s, c i • μ i t) (∑ i ∈ s, c i • ν i t)) l (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ i ∈ s, c i * QuantumZipper.TV.tvDist (μ i t) (ν i t))
      l (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, Finset.sum_const_zero] using
      (tendsto_finsetSum s fun i hi =>
        (ENNReal.continuousAt_const_mul (a := c i) (b := 0) (Or.inl (hc i hi))).tendsto.comp (h i hi))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun t => (tvDist_finset_sum_le s _ _).trans
      (Finset.sum_le_sum fun i _ => tvDist_smul_le (c i) (μ i t) (ν i t))

end LatticeProb
