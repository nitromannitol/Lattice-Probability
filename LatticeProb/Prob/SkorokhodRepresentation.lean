/-
Built on modules adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
-/
import LatticeProb.Prob.Skorokhod

/-!
# Skorokhod representation theorem, almost sure form

This file packages the construction of `LatticeProb.Skorokhod` into a single statement. Let `S`
be a separable pseudo-metric space whose measurable sets contain the open sets, and let
`μs n` and `μ` be probability measures on `S` with `μs n → μ` weakly. Then there is a probability
space carrying random elements `Y n` with laws `μs n` and a random element `Y₀` with law `μ`, such
that `Y n → Y₀` almost surely.

The probability space is `SkΩ S` with the measure `SkData.prob`, where `SkData` is the data of the
construction. The laws come from `SkData.map_X'` and `SkData.prob_coord`, and the almost sure
convergence comes from `SkData.prob_good_compl`, `SkData.prob_bad` and `SkData.tendsto_X'`.

The file proves only the almost sure form. It does not modify the random elements on a null set,
so it does not claim pointwise convergence on the whole space.
-/

open MeasureTheory Set Filter Topology

universe u

namespace LatticeProb.Skorokhod

/-- **Skorokhod representation theorem, almost sure form.** Let `S` be a separable pseudo-metric
space whose measurable sets include the open sets (`OpensMeasurableSpace S`). If probability
measures `μs n` on `S` converge weakly to a probability measure `μ`, that is
`Tendsto μs atTop (𝓝 μ)` in the weak topology on `ProbabilityMeasure S`, then there exist a
probability space `(Ω, P)`, measurable maps `Y n : Ω → S` with law `μs n` for every `n`, and a
measurable map `Y₀ : Ω → S` with law `μ`, such that `Y n ω → Y₀ ω` for `P`-almost every `ω`. -/
theorem exists_skorokhod_representation
    {S : Type u} [MeasurableSpace S] [PseudoMetricSpace S] [OpensMeasurableSpace S]
    [TopologicalSpace.SeparableSpace S]
    {μ : ProbabilityMeasure S} {μs : ℕ → ProbabilityMeasure S}
    (h : Tendsto μs atTop (𝓝 μ)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y : ℕ → Ω → S) (Y₀ : Ω → S),
      (∀ n, Measurable (Y n)) ∧ Measurable Y₀ ∧
      (∀ n, P.map (Y n) = (μs n : Measure S)) ∧ P.map Y₀ = (μ : Measure S) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω)) := by
  obtain ⟨D⟩ := LatticeProb.Skorokhod.exists_skData h
  have hY₀ : Measurable fun ω : SkΩ S => ω.1 none :=
    (measurable_pi_apply none).comp measurable_fst
  refine ⟨SkΩ S, inferInstance, D.prob, inferInstance, fun n => D.X' n, fun ω => ω.1 none,
    D.measurable_X', hY₀, D.map_X', ?_, ?_⟩
  · ext U hU
    rw [Measure.map_apply hY₀ hU]
    exact D.prob_coord none hU
  · rw [ae_iff]
    refine measure_mono_null (t := (D.good)ᶜ ∪ D.bad) ?_
      (measure_union_null D.prob_good_compl D.prob_bad)
    intro ω hω
    rw [mem_setOf_eq] at hω
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hc
    exact hω (D.tendsto_X' hc.1 hc.2)

namespace SkorokhodRepresentationExample

-- Nonvacuity: the constant sequence `μs n = μ` satisfies the weak convergence hypothesis.
example (μ : ProbabilityMeasure ℝ) :=
  exists_skorokhod_representation (μ := μ) (μs := fun _ => μ) tendsto_const_nhds

end SkorokhodRepresentationExample

end LatticeProb.Skorokhod
