import LatticeProb.Prob.FiniteProductTV

/-! Convergence in total variation for finite products. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Finite products of probability measures converge in total variation when
all their factors converge in total variation. Both families may vary. -/
theorem tendsto_tvDist_pi_fin {α τ : Type*} [MeasurableSpace α]
    {l : Filter τ} (n : ℕ) (μ ν : Fin n → τ → Measure α)
    [∀ i t, IsProbabilityMeasure (μ i t)] [∀ i t, IsProbabilityMeasure (ν i t)]
    (h : ∀ i, Tendsto (fun t => QuantumZipper.TV.tvDist (μ i t) (ν i t)) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (Measure.pi fun i => μ i t) (Measure.pi fun i => ν i t)) l (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ i, QuantumZipper.TV.tvDist (μ i t) (ν i t))
      l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using (tendsto_finsetSum Finset.univ fun i _ => h i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun t => tvDist_pi_fin_le_sum n (fun i => μ i t) (fun i => ν i t)

end LatticeProb
