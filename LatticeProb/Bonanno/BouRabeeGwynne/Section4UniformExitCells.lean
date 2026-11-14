/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.Section4UniformExitCells at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.Section4UniformExitTopology
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Uniform continuity-set comparison for a compact family of exit laws. -/

open MeasureTheory Filter
open scoped Topology Classical

namespace BouRabeeGwynne

/-- Evaluation on a common continuity set is continuous along a continuous
probability kernel. -/
theorem continuous_probability_cell_mass {d : ℕ} {P : Type*} [TopologicalSpace P]
    (ν : P → ProbabilityMeasure (Euc d)) (hν : Continuous ν) (S : Set (Euc d))
    (hnull : ∀ z : P, (ν z : Measure (Euc d)) (frontier S) = 0) :
    Continuous (fun z => ((ν z : Measure (Euc d)) S).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (ENNReal.tendsto_toReal (measure_ne_top _ S)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (hν.tendsto z) (hnull z))

/-- Uniform LP comparison with a continuous compact family gives uniform
mass comparison on any fixed set whose frontier is null for every limiting
law. The null-frontier hypothesis is essential for this conclusion. -/
theorem uniform_cell_mass_error_of_uniform_levyProkhorov_error
    {d : ℕ} {P : Type*} [PseudoMetricSpace P] [CompactSpace P]
    (V : ℕ → Type*) (p : ∀ n, V n → P)
    (μ : ∀ n, V n → ProbabilityMeasure (Euc d))
    (ν : P → ProbabilityMeasure (Euc d)) (hν : Continuous ν)
    (hLP : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      levyProkhorovDist (μ n v : Measure (Euc d))
        (ν (p n v) : Measure (Euc d)) < ε)
    (S : Set (Euc d))
    (hnull : ∀ z : P, (ν z : Measure (Euc d)) (frontier S) = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      |((μ n v : Measure (Euc d)) S).toReal -
        ((ν (p n v) : Measure (Euc d)) S).toReal| < ε := by
  intro ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, ∃ v : V n,
      ε ≤ |((μ n v : Measure (Euc d)) S).toReal -
        ((ν (p n v) : Measure (Euc d)) S).toReal| := by
    simpa only [Filter.Frequently, not_exists, not_le] using hnot
  obtain ⟨σ, hσ, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose v hv using hbad
  obtain ⟨z, φ, hφ, hp⟩ := SeqCompactSpace.tendsto_subseq (fun j => p (σ j) (v j))
  let μs : ℕ → ProbabilityMeasure (Euc d) := fun j => μ (σ (φ j)) (v (φ j))
  let νs : ℕ → ProbabilityMeasure (Euc d) := fun j => ν (p (σ (φ j)) (v (φ j)))
  have hn : Tendsto (σ ∘ φ) atTop atTop := hσ.tendsto_atTop.comp hφ.tendsto_atTop
  have hνs : Tendsto νs atTop (𝓝 (ν z)) := by
    simpa only [νs, Function.comp_def] using (hν.tendsto z).comp hp
  have hνLP : Tendsto (fun j => LevyProkhorov.ofMeasure (νs j)) atTop
      (𝓝 (LevyProkhorov.ofMeasure (ν z))) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hνs
  have hdist : Tendsto (fun j => dist (LevyProkhorov.ofMeasure (μs j))
      (LevyProkhorov.ofMeasure (νs j))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hn.eventually (hLP η hη)] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    simpa only [LevyProkhorov.dist_probabilityMeasure_def, μs, νs, Function.comp_apply] using
      hj (v (φ j))
  have hμLP : Tendsto (fun j => LevyProkhorov.ofMeasure (μs j)) atTop
      (𝓝 (LevyProkhorov.ofMeasure (ν z))) :=
    hνLP.congr_dist (by simpa only [dist_comm] using hdist)
  have hμs : Tendsto μs atTop (𝓝 (ν z)) :=
    (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp hμLP
  have hμmass : Tendsto (fun j => ((μs j : Measure (Euc d)) S).toReal) atTop
      (𝓝 (((ν z : Measure (Euc d)) S).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ S)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμs (hnull z))
  have hνmass : Tendsto (fun j => ((νs j : Measure (Euc d)) S).toReal) atTop
      (𝓝 (((ν z : Measure (Euc d)) S).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ S)).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hνs (hnull z))
  have herr : Tendsto (fun j => ((μs j : Measure (Euc d)) S).toReal -
      ((νs j : Measure (Euc d)) S).toReal) atTop (𝓝 0) := by
    simpa only [sub_self] using hμmass.sub hνmass
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp herr ε hε).exists
  have hsmall : |((μs j : Measure (Euc d)) S).toReal -
      ((νs j : Measure (Euc d)) S).toReal| < ε := by
    simpa only [Real.dist_eq, sub_zero] using hj
  exact (not_lt_of_ge (hv (φ j))) hsmall

/-- A single starting-point modulus works simultaneously for a fixed finite
family of common continuity cells. Both starting points lie in the compact
parameter space. -/
theorem uniform_nearby_cell_mass_error_of_uniform_levyProkhorov_error
    {d : ℕ} {P : Type*} [PseudoMetricSpace P] [CompactSpace P]
    (V : ℕ → Type*) (p : ∀ n, V n → P)
    (μ : ∀ n, V n → ProbabilityMeasure (Euc d))
    (ν : P → ProbabilityMeasure (Euc d)) (hν : Continuous ν)
    (hLP : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      levyProkhorovDist (μ n v : Measure (Euc d))
        (ν (p n v) : Measure (Euc d)) < ε)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc d))
    (hnull : ∀ i, ∀ z : P, (ν z : Measure (Euc d)) (frontier (S i)) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ v : V n, ∀ z : P, dist (p n v) z ≤ δ → ∀ i,
        |((μ n v : Measure (Euc d)) (S i)).toReal -
          ((ν z : Measure (Euc d)) (S i)).toReal| ≤ ε := by
  intro ε hε
  let F : P → ι → ℝ := fun z i => ((ν z : Measure (Euc d)) (S i)).toReal
  have hF : Continuous F := continuous_pi (fun i =>
    continuous_probability_cell_mass ν hν (S i) (hnull i))
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hF) (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hsame : ∀ᶠ n in atTop, ∀ i, ∀ v : V n,
      |((μ n v : Measure (Euc d)) (S i)).toReal -
        ((ν (p n v) : Measure (Euc d)) (S i)).toReal| < ε / 2 :=
    Filter.eventually_all.mpr (fun i =>
      uniform_cell_mass_error_of_uniform_levyProkhorov_error V p μ ν hν hLP
        (S i) (hnull i) (ε / 2) (half_pos hε))
  filter_upwards [hsame] with n hn
  intro v z hz i
  have hnear : dist (F (p n v)) (F z) < ε / 2 :=
    hcontrol (hz.trans_lt (half_lt_self hδ))
  have hmass : |F (p n v) i - F z i| < ε / 2 := by
    simpa only [Real.dist_eq] using (dist_le_pi_dist (F (p n v)) (F z) i).trans_lt hnear
  calc
    _ ≤ |((μ n v : Measure (Euc d)) (S i)).toReal - F (p n v) i| +
        |F (p n v) i - F z i| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hn i v).le hmass.le
    _ = ε := add_halves ε

end BouRabeeGwynne
