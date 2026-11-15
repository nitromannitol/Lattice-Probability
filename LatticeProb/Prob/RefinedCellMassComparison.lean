import LatticeProb.Prob.FiniteDomainCellComparison
import LatticeProb.Prob.PartitionSelectorRefinement
import LatticeProb.Prob.SkorokhodPartition

/-! # Uniform mass comparison for selector refinements -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LatticeProb.PartitionSelector

/-- Uniform convergence of endpoint laws gives a common nearby-start mass bound
for a finite selector refinement, provided both the original cells and all selector
fibers have null frontiers for each reference law. -/
theorem finite_uniform_nearby_fiberCell_mass_error
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (BouRabeeGwynne.Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (BouRabeeGwynne.Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (BouRabeeGwynne.Euc d))
        (ν j (p j n v) : Measure (BouRabeeGwynne.Euc d)) < ε)
    {ι A : Type*} [Fintype ι] [Fintype A]
    (E : ι → Set (BouRabeeGwynne.Euc d)) (f : BouRabeeGwynne.Euc d → Option A)
    (hE : ∀ j i z, (ν j z : Measure (BouRabeeGwynne.Euc d)) (frontier (E i)) = 0)
    (hf : ∀ j a z, (ν j z : Measure (BouRabeeGwynne.Euc d))
      (frontier (f ⁻¹' {a})) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ q : ι × Option A,
        |((μ j n v : Measure (BouRabeeGwynne.Euc d)) (fiberCell E f q)).toReal -
          ((ν j z : Measure (BouRabeeGwynne.Euc d)) (fiberCell E f q)).toReal| ≤ ε := by
  apply finite_uniform_nearby_cell_mass_error P V p μ ν hν hLP (fiberCell E f) _ hε
  intro j q z
  change (ν j z : Measure (BouRabeeGwynne.Euc d))
    (frontier (E q.1 ∩ f ⁻¹' {q.2})) = 0
  exact Skorokhod.measure_frontier_inter_null (ν j z : Measure (BouRabeeGwynne.Euc d))
    (hE j q.1 z) (hf j q.2 z)

end LatticeProb.PartitionSelector
