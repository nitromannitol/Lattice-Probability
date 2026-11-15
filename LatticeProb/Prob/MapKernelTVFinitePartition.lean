import LatticeProb.Prob.TVFiniteSumLimit
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Finite assembly of total variation convergence for images and kernels. -/

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal Topology

namespace LatticeProb

/-- Convergence of map and kernel images passes to a finite sum of measures. -/
theorem tendsto_tvDist_map_comp_finset_sum
    {α β ι τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (s : Finset ι) (μ : ι → Measure α) (f : τ → α → β)
    (hf : ∀ t, Measurable (f t)) (κ : τ → Kernel α β)
    (h : ∀ i ∈ s, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ i).map (f t)) ((κ t) ∘ₘ μ i)) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((∑ i ∈ s, μ i).map (f t)) ((κ t) ∘ₘ (∑ i ∈ s, μ i))) l (𝓝 0) := by
  classical
  have hcomp (t : τ) (u : Finset ι) :
      (κ t) ∘ₘ (∑ i ∈ u, μ i) = ∑ i ∈ u, (κ t) ∘ₘ μ i := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert i u hi ih => simp only [Finset.sum_insert hi, Measure.comp_add, ih]
  have hs := tendsto_tvDist_finset_sum_smul s (fun _ => 1)
    (fun _ _ => ENNReal.one_ne_top) (fun i t => (μ i).map (f t))
    (fun i t => (κ t) ∘ₘ μ i) h
  simp only [one_smul] at hs
  convert hs using 1
  funext t
  rw [Measure.map_finset_sum (hf t).aemeasurable]
  rw [hcomp]

/-- Convergence on disjoint measurable pieces passes to their finite union. -/
theorem tendsto_tvDist_map_comp_restrict_finset_union
    {α β ι τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (s : Finset ι) (μ : Measure α) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hd : (s : Set ι).Pairwise (Disjoint on A))
    (f : τ → α → β) (hf : ∀ t, Measurable (f t)) (κ : τ → Kernel α β)
    (h : ∀ i ∈ s, Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.restrict (A i)).map (f t)) ((κ t) ∘ₘ (μ.restrict (A i)))) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.restrict (⋃ i ∈ s, A i)).map (f t))
      ((κ t) ∘ₘ (μ.restrict (⋃ i ∈ s, A i)))) l (𝓝 0) := by
  rw [Measure.restrict_biUnion_finset hd hA]
  rw [Measure.sum_coe_finset s (fun i => μ.restrict (A i))]
  exact tendsto_tvDist_map_comp_finset_sum s (fun i => μ.restrict (A i)) f hf κ h

end LatticeProb
