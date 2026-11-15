import LatticeProb.Prob.FiniteDomainCellComparison
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellCouplingError

/-! # Uniform coupling bounds for continuity-cell partitions -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace LatticeProb

/-- Uniform convergence of endpoint laws and continuity of their limits give a
uniform bound for a finite-partition coupling at nearby starting points. The
reference laws must give full mass to the union of the continuity cells. -/
theorem finite_uniform_nearby_partition_coupling_bad_le
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc d))
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (S i)) = 0)
    (hcover : ∀ j z, (ν j z : Measure (Euc d)) (⋃ i, S i) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ B : Set (Euc d × Euc d),
        (∀ i, Disjoint B (S i ×ˢ S i)) →
        finitePartitionCoupling (μ j n v : Measure (Euc d))
          (ν j z : Measure (Euc d)) S S B ≤
            ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  obtain ⟨δ, hδ, hcompare⟩ :=
    finite_uniform_nearby_cell_mass_error P V p μ ν hν hLP S hnull hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hcompare] with n hn
  intro j v z hz B hB
  exact finitePartitionCoupling_bad_le_of_cell_error _ _ hS hS hdisj hdisj
    (hcover j z) (le_of_lt hε) (hn j v z hz) B hB

end LatticeProb
