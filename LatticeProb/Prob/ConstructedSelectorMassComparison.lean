import LatticeProb.Prob.RefinedCellMassComparison
import LatticeProb.Prob.CellSelectorFrontier

/-! # Mass comparison for constructed finite selectors -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace LatticeProb.PartitionSelector

/-- Uniform mass comparison for cells refined by a selector constructed from
another finite family of disjoint continuity cells. -/
theorem finite_uniform_nearby_constructed_fiberCell_mass_error
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    {ι κ A : Type*} [Fintype ι] [Fintype κ] [Fintype A]
    (E : ι → Set (Euc d)) (F : κ → Set (Euc d)) (select : κ → Option A)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hE : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (E i)) = 0)
    (hF : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (F i)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ q : ι × Option A,
        |((μ j n v : Measure (Euc d)) (fiberCell E (cellSelector F select) q)).toReal -
          ((ν j z : Measure (Euc d)) (fiberCell E (cellSelector F select) q)).toReal| ≤ ε := by
  apply finite_uniform_nearby_fiberCell_mass_error P V p μ ν hν hLP E
    (cellSelector F select) hE _ hε
  intro j a z
  exact cellSelector_fiber_frontier_null (ν j z : Measure (Euc d)) F select hdisj
    (fun i => hF j i z) a

end LatticeProb.PartitionSelector
