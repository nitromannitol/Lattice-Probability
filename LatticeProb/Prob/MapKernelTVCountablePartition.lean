import LatticeProb.Prob.MapKernelTVFinitePartition
import LatticeProb.Prob.MapKernelTVExhaustion

/-! Countable assembly of total variation convergence for images and kernels. -/

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal Topology

namespace LatticeProb

/-- Convergence on a countable measurable partition transfers to a finite measure. -/
theorem tendsto_tvDist_map_comp_of_countable_partition
    {α β τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (μ : Measure α) [IsFiniteMeasure μ] (A : ℕ → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) (hcover : (⋃ i, A i) = univ)
    (f : τ → α → β) (hf : ∀ t, Measurable (f t)) (κ : τ → Kernel α β)
    (hκ : ∀ t, IsMarkovKernel (κ t))
    (h : ∀ i, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.restrict (A i)).map (f t)) ((κ t) ∘ₘ (μ.restrict (A i)))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist (μ.map (f t))
      ((κ t) ∘ₘ μ)) l (𝓝 0) := by
  let B : ℕ → Set α := fun k => ⋃ i ∈ Finset.range k, A i
  have hB (k : ℕ) : MeasurableSet (B k) := by
    exact Finset.measurableSet_biUnion _ (fun i _ => hA i)
  have hmono : Monotone B := by
    intro i j hij x hx
    simp only [B, mem_iUnion] at hx ⊢
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨n, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hij), hx⟩
  have hBcover : (⋃ k, B k) = univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i + 1, Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self i), hi⟩⟩⟩
  apply tendsto_tvDist_map_comp_of_exhaustion μ f hf κ hκ B hB hmono hBcover
  intro k
  exact tendsto_tvDist_map_comp_restrict_finset_union (Finset.range k) μ A hA
    (fun _ _ _ _ hne => hd hne) f hf κ (fun i _ => h i)

end LatticeProb
