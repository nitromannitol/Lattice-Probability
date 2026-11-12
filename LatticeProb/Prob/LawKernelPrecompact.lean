/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Precompactness of equicontinuous families of continuous maps into probability measures

The Arzelà–Ascoli step for continuous maps `Z → Prob(Ω)` ("kernels"), with `Prob(Ω)` carrying the
Lévy–Prokhorov metric.

* `LatticeProb.isCompact_closure_of_equicontinuous_of_pointwise_compact`: an equicontinuous set of
  continuous maps `Z → Y` (`Y` metric, `Z` compactly coherent, e.g. locally compact) whose values
  at each point lie in a compact set has compact closure in the compact-open topology.
* `LatticeProb.equicontinuous_of_ball_modulus`: equicontinuity from the condition "for each
  `L > 1` there is `δ` such that `dist (f z) (f w) ≤ 1 / L` for `z, w` in the ball of radius `L`
  with `dist z w ≤ δ`".
* `LatticeProb.isCompact_closure_of_equicontinuous_of_tight`: for `Ω` separable metric, an
  equicontinuous set of continuous maps `Z → Prob(Ω)` (Lévy–Prokhorov metric) whose values at
  each point form a tight family of measures has compact closure.
-/

open Filter Topology Set MeasureTheory Metric

noncomputable section

namespace LatticeProb

/-- **Arzelà–Ascoli for maps into a metric space.**  An equicontinuous set `K` of continuous maps
`Z → Y`, such that for each `z` the values `f z`, `f ∈ K`, lie in a fixed compact set, has compact
closure in `C(Z, Y)` (compact-open topology). -/
theorem isCompact_closure_of_equicontinuous_of_pointwise_compact
    {Z Y : Type*} [TopologicalSpace Z] [CompactlyCoherentSpace Z] [MetricSpace Y]
    (K : Set C(Z, Y)) (heq : Equicontinuous ((↑) : K → Z → Y))
    (hpt : ∀ z : Z, ∃ Q : Set Y, IsCompact Q ∧ ∀ f ∈ K, f z ∈ Q) :
    IsCompact (closure K) := by
  have hemb : Topology.IsEmbedding (UniformOnFun.ofFun {S : Set Z | IsCompact S} ∘
      ((↑) : C(Z, Y) → Z → Y)) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding
  have hclosed : IsClosed (range (UniformOnFun.ofFun {S : Set Z | IsCompact S} ∘
      ((↑) : C(Z, Y) → Z → Y))) := by
    have h : range (UniformOnFun.ofFun {S : Set Z | IsCompact S} ∘ ((↑) : C(Z, Y) → Z → Y)) =
        {f : UniformOnFun Z Y {S : Set Z | IsCompact S} |
          Continuous (UniformOnFun.toFun {S : Set Z | IsCompact S} f)} := by
      ext f
      constructor
      · rintro ⟨g, rfl⟩
        exact g.continuous
      · intro hf
        exact ⟨⟨_, hf⟩, rfl⟩
    rw [h]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {S : Set Z | IsCompact S}) (fun S hS => hS) ⟨hemb, hclosed⟩ (s := K) ?_ ?_
  · intro S _
    exact heq.equicontinuousOn S
  · intro S _ z _
    obtain ⟨Q, hQ, hQK⟩ := hpt z
    exact ⟨Q, hQ, fun f hf => hQK f hf⟩

/-- **Equicontinuity from a ball modulus.**  Suppose that for each `L > 1` there is `δ > 0` such
that every `f ∈ K` satisfies `dist (f z) (f w) ≤ 1 / L` whenever `z, w` lie in the open ball of
radius `L` around `z₀` and `dist z w ≤ δ`.  Then `K` is equicontinuous. -/
theorem equicontinuous_of_ball_modulus {Z Y : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace Y]
    (K : Set (Z → Y)) (z₀ : Z)
    (h : ∀ L : ℝ, 1 < L → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ K, ∀ z w : Z, dist z z₀ < L → dist w z₀ < L →
      dist z w ≤ δ → dist (f z) (f w) ≤ 1 / L) :
    Equicontinuous ((↑) : K → Z → Y) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / ε) (dist x z₀ + 1))
  have hn1 : 1 / ε < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn2 : dist x z₀ + 1 < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hd0 : 0 ≤ dist x z₀ := dist_nonneg
  have hn0 : (0 : ℝ) < n := lt_trans (one_div_pos.2 hε) hn1
  have hnL : 1 < (n : ℝ) := by linarith
  obtain ⟨δ, hδ, hδK⟩ := h n hnL
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy f => ?_⟩
  have hy1 : dist y x < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : dist y x < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  have hyz : dist y z₀ < n := by
    have := dist_triangle y x z₀
    linarith
  have hxz : dist x z₀ < n := by linarith
  have hmain : dist (f.1 x) (f.1 y) ≤ 1 / (n : ℝ) :=
    hδK f.1 f.2 x y hxz hyz (by rw [dist_comm]; exact hy1.le)
  have hlt : 1 / (n : ℝ) < ε := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hε] at hn1
    linarith
  exact lt_of_le_of_lt hmain hlt

/-- **Precompactness of equicontinuous families of laws.**  Let `Ω` be a separable metric space
with its Borel σ-algebra, and give the probability measures on `Ω` the Lévy–Prokhorov metric.  An
equicontinuous set `K` of continuous maps `Z → Prob(Ω)` such that, for each `z`, the measures
`f z`, `f ∈ K`, form a tight family has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_equicontinuous_of_tight
    {Z Ω : Type*} [TopologicalSpace Z] [CompactlyCoherentSpace Z]
    [MetricSpace Ω] [TopologicalSpace.SeparableSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    (K : Set C(Z, LevyProkhorov (ProbabilityMeasure Ω)))
    (heq : Equicontinuous ((↑) : K → Z → LevyProkhorov (ProbabilityMeasure Ω)))
    (htight : ∀ z : Z, IsTightMeasureSet
      {μ : Measure Ω | ∃ f ∈ K, μ = ((LevyProkhorov.toMeasure (f z) : ProbabilityMeasure Ω) :
        Measure Ω)}) :
    IsCompact (closure K) := by
  refine isCompact_closure_of_equicontinuous_of_pointwise_compact K heq fun z => ?_
  set S : Set (ProbabilityMeasure Ω) :=
    {ν | ∃ f ∈ K, ν = LevyProkhorov.toMeasure (f z)} with hS
  have hSt : IsTightMeasureSet {((ν : ProbabilityMeasure Ω) : Measure Ω) | ν ∈ S} := by
    have h : {((ν : ProbabilityMeasure Ω) : Measure Ω) | ν ∈ S} =
        {μ : Measure Ω | ∃ f ∈ K, μ = ((LevyProkhorov.toMeasure (f z) : ProbabilityMeasure Ω) :
          Measure Ω)} := by
      ext μ
      constructor
      · rintro ⟨ν, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f, hf, rfl⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [h]
    exact htight z
  have hcl : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet (E := Ω) (S := S) hSt
  refine ⟨LevyProkhorov.probabilityMeasureHomeomorph '' closure S,
    hcl.image LevyProkhorov.probabilityMeasureHomeomorph.continuous, fun f hf => ?_⟩
  exact ⟨LevyProkhorov.toMeasure (f z), subset_closure ⟨f, hf, rfl⟩, rfl⟩

end LatticeProb
