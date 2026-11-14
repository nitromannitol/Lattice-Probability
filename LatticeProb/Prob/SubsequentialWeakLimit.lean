import Mathlib

/-!
# Subsequential weak limits of tight sequences of probability measures

Prokhorov's theorem (Mathlib: `isCompact_closure_of_isTightMeasureSet`) says that the closure of a tight set
of probability measures is compact for the topology of convergence in distribution. On a separable
pseudo-metrizable space this topology is pseudo-metrizable, so compact sets are sequentially compact: a tight
sequence of probability measures has a subsequence converging in distribution.

## Main result

* `exists_subseq_tendsto_integral_of_isTightMeasureSet`: if the probability measures `μ n` on a separable
  metrizable Borel space form a tight set, then along some subsequence `∫ f dμ (φ k) → ∫ f dν` for every
  bounded continuous `f`, with `ν` a probability measure.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LatticeProb

/-- **Sequential Prokhorov theorem.** A tight sequence of probability measures on a separable
pseudo-metrizable Hausdorff Borel space has a subsequence converging in distribution to a probability
measure: `∫ f dμ (φ k) → ∫ f dν` for every bounded continuous `f`. -/
theorem exists_subseq_tendsto_integral_of_isTightMeasureSet {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [T2Space E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E]
    [BorelSpace E] (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (h : IsTightMeasureSet (Set.range μ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : Measure E, IsProbabilityMeasure ν ∧
      ∀ f : E →ᵇ ℝ, Tendsto (fun k => ∫ x, f x ∂μ (φ k)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  let q : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  have hsets : {((p : ProbabilityMeasure E) : Measure E) | p ∈ Set.range q} = Set.range μ := by
    ext ν
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨q n, ⟨n, rfl⟩, rfl⟩
  have hcl : IsCompact (closure (Set.range q)) :=
    isCompact_closure_of_isTightMeasureSet (by rw [hsets]; exact h)
  obtain ⟨p, -, φ, hφ, hconv⟩ := hcl.tendsto_subseq (x := q) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, hφ, (p : Measure E), p.prop, fun f => ?_⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) f

end LatticeProb
