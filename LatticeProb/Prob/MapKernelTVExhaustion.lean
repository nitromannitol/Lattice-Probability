import LatticeProb.Prob.MapKernelTVApproximation
import LatticeProb.Prob.PhaseExhaustion

/-! Total variation convergence through finite-measure approximations. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace LatticeProb

/-- Comparison of measurable images with Markov-kernel images transfers from
arbitrarily close finite measures. -/
theorem tendsto_tvDist_map_comp_of_exists_approx
    {α β τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (μ : Measure α) [IsFiniteMeasure μ] (f : τ → α → β)
    (hf : ∀ t, Measurable (f t)) (κ : τ → Kernel α β)
    (hκ : ∀ t, IsMarkovKernel (κ t))
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ν : Measure α,
      IsFiniteMeasure ν ∧ QuantumZipper.TV.tvDist μ ν < ε ∧
      Tendsto (fun t => QuantumZipper.TV.tvDist (ν.map (f t))
        ((κ t) ∘ₘ ν)) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist (μ.map (f t))
      ((κ t) ∘ₘ μ)) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hh : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hq : 0 < (ε / 2) / 2 := ENNReal.half_pos hh.ne'
  obtain ⟨ν, hfin, hnear, hphase⟩ := happrox _ hq
  let : IsFiniteMeasure ν := hfin
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hphase _ hh] with t ht
  let : IsMarkovKernel (κ t) := hκ t
  calc
    _ ≤ QuantumZipper.TV.tvDist (ν.map (f t)) ((κ t) ∘ₘ ν) +
        (QuantumZipper.TV.tvDist μ ν + QuantumZipper.TV.tvDist μ ν) :=
      tvDist_map_comp_le_of_approx μ ν (hf t) (κ t)
    _ ≤ ε / 2 + ((ε / 2) / 2 + (ε / 2) / 2) :=
      add_le_add ht (add_le_add hnear.le hnear.le)
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- Convergence on an increasing measurable cover transfers to a finite
measure. -/
theorem tendsto_tvDist_map_comp_of_exhaustion
    {α β τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (μ : Measure α) [IsFiniteMeasure μ] (f : τ → α → β)
    (hf : ∀ t, Measurable (f t)) (κ : τ → Kernel α β)
    (hκ : ∀ t, IsMarkovKernel (κ t))
    (B : ℕ → Set α) (hB : ∀ k, MeasurableSet (B k))
    (hmono : Monotone B) (hcover : (⋃ k, B k) = univ)
    (hphase : ∀ k, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.restrict (B k)).map (f t)) ((κ t) ∘ₘ (μ.restrict (B k)))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist (μ.map (f t))
      ((κ t) ∘ₘ μ)) l (𝓝 0) := by
  apply tendsto_tvDist_map_comp_of_exists_approx μ f hf κ hκ
  intro ε hε
  obtain ⟨k, hk⟩ := exists_restrict_tvDist_lt_of_iUnion_eq_univ μ B hB hmono hcover hε
  exact ⟨μ.restrict (B k), inferInstance, hk, hphase k⟩

end LatticeProb
