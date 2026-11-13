/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.LawKernelPrecompact
import LatticeProb.Prob.PathSpaceTightness
import LatticeProb.Prob.PathSpaceDUnif

/-!
# A compactness criterion for continuous families of path laws

Let `Z` and `E` be proper metric spaces.  A *path kernel* is a continuous map
`f : Z → Prob(C(ℝ≥0, E))`, where the space `C(ℝ≥0, E)` of continuous paths carries the local
uniform metric `dUnif` (`LatticeProb.dUnifMetricSpace`) and `Prob(C(ℝ≥0, E))` the Lévy–Prokhorov
metric; the space `C(Z, Prob(C(ℝ≥0, E)))` carries the compact-open topology (uniform convergence
on compact sets).

* `LatticeProb.isCompact_closure_of_laws_and_paths_equicontinuous`: a set `K` of path kernels has
  compact closure if
  1. (equicontinuity of laws) for each `L > 1` there is `δ > 0` such that for every `f ∈ K` and all
     `z, w` in the ball of radius `L` with `dist z w ≤ δ`, the Lévy–Prokhorov distance between
     `f z` and `f w` is at most `1 / L`;
  2. (starting points) for each `z`, the starting points of the paths of the laws `f z`, `f ∈ K`,
     are tight;
  3. (equicontinuity of paths) for each `z` and `L > 0` there is `δ > 0` such that for every
     `f ∈ K` the path of law `f z` has, with probability at least `1 - 1 / L`, modulus of
     continuity at most `1 / L` at scale `δ` on `[0, L]`.

This is the Arzelà–Ascoli and Prokhorov compactness criterion used to prove tightness of random
walk path laws; it combines `isCompact_closure_of_equicontinuous_of_tight` with
`isTightMeasureSet_of_pathModuli`.
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {Z E : Type*}

/-- **Compactness criterion for path kernels.**  Let `Z`, `E` be proper metric spaces and `K` a set
of continuous maps `Z → Prob(C(ℝ≥0, E))` (Lévy–Prokhorov metric for the local uniform metric on
paths).  If the laws are equicontinuous on balls, the starting points of the paths are tight at each
`z` (around `x₀ z`) and the path moduli of continuity are uniformly small at each `z`, then `K` has
compact closure in `C(Z, Prob(C(ℝ≥0, E)))`. -/
theorem isCompact_closure_of_laws_and_paths_equicontinuous
    [MetricSpace Z] [ProperSpace Z] [MetricSpace E] [ProperSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    (K : Set C(Z, LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E)))) (z₀ : Z) (x₀ : Z → E)
    (hlaws : ∀ L : ℝ, 1 < L → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ K, ∀ z w : Z, dist z z₀ < L → dist w z₀ < L →
      dist z w ≤ δ → dist (f z) (f w) ≤ 1 / L)
    (hstart : ∀ z : Z, ∀ ζ : ℝ, 0 < ζ → ∃ R : ℝ, ∀ f ∈ K,
      ((LevyProkhorov.toMeasure (f z) : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E))
        {g : C(ℝ≥0, E) | R < dist (g 0) (x₀ z)} ≤ ENNReal.ofReal ζ)
    (hpaths : ∀ z : Z, ∀ L : ℝ, 0 < L → ∃ δ : ℝ≥0, 0 < δ ∧ ∀ f ∈ K,
      ((LevyProkhorov.toMeasure (f z) : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E))
        (pathModulusFailure L δ) ≤ ENNReal.ofReal (1 / L)) :
    IsCompact (closure K) := by
  have heq : Equicontinuous ((↑) : K → Z → LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E))) := by
    have h0 := equicontinuous_of_ball_modulus
      (((↑) : C(Z, LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E))) → Z → _) '' K) z₀ (by
        intro L hL
        obtain ⟨δ, hδ, h⟩ := hlaws L hL
        refine ⟨δ, hδ, ?_⟩
        rintro _ ⟨f, hf, rfl⟩ z w hz hw hzw
        exact h f hf z w hz hw hzw)
    exact h0.comp (fun f : K => (⟨(f.1 : Z → _), ⟨f.1, f.2, rfl⟩⟩ :
      (((↑) : C(Z, LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E))) → Z → _) '' K)))
  refine isCompact_closure_of_equicontinuous_of_tight K heq fun z => ?_
  refine isTightMeasureSet_of_pathModuli _ (x₀ z) ?_ ?_
  · intro ζ hζ
    obtain ⟨R, hR⟩ := hstart z ζ hζ
    refine ⟨R, ?_⟩
    rintro μ ⟨f, hf, rfl⟩
    exact hR f hf
  · intro L hL
    obtain ⟨δ, hδ, h⟩ := hpaths z L hL
    refine ⟨δ, hδ, ?_⟩
    rintro μ ⟨f, hf, rfl⟩
    exact h f hf

end LatticeProb
