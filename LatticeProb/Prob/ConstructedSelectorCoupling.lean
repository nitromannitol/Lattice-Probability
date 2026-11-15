import LatticeProb.Prob.ConstructedSelectorMassComparison
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellCouplingError

/-! # Coupling on constructed selector refinements -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace LatticeProb.PartitionSelector

/-- Uniform coupling on a partition refined by a selector constructed from
another finite family of disjoint continuity cells. -/
theorem finite_uniform_nearby_constructed_fiberCell_coupling_bad_le
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
    [MeasurableSpace (Option κ)] [MeasurableSingletonClass (Option κ)]
    [MeasurableSpace (Option A)] [MeasurableSingletonClass (Option A)]
    (E : ι → Set (Euc d)) (F : κ → Set (Euc d)) (select : κ → Option A)
    (hEm : ∀ i, MeasurableSet (E i)) (hFm : ∀ i, MeasurableSet (F i))
    (hEd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hFd : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hE : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (E i)) = 0)
    (hF : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (F i)) = 0)
    (hcover : ∀ j z, (ν j z : Measure (Euc d)) (⋃ i, E i) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ → ∀ B : Set (Euc d × Euc d),
        (∀ q, Disjoint B (fiberCell E (cellSelector F select) q ×ˢ
          fiberCell E (cellSelector F select) q)) →
        finitePartitionCoupling (μ j n v : Measure (Euc d))
          (ν j z : Measure (Euc d)) (fiberCell E (cellSelector F select))
          (fiberCell E (cellSelector F select)) B ≤
            ENNReal.ofReal ((Fintype.card (ι × Option A) : ℝ) * ε) := by
  obtain ⟨δ, hδ, hcompare⟩ :=
    finite_uniform_nearby_constructed_fiberCell_mass_error P V p μ ν hν hLP E F select
      hFd hE hF hε
  have hm : ∀ q, MeasurableSet (fiberCell E (cellSelector F select) q) :=
    measurableSet_fiberCell E (cellSelector F select) hEm
      (measurable_cellSelector F select hFd hFm)
  have hd := pairwise_disjoint_fiberCell E (cellSelector F select) hEd
  have hc (j : J) (z : P j) :
      (ν j z : Measure (Euc d)) (⋃ q, fiberCell E (cellSelector F select) q) = 1 := by
    have heq : (⋃ q, fiberCell E (cellSelector F select) q) = ⋃ i, E i := by
      ext x
      exact mem_iUnion_fiberCell_iff E (cellSelector F select) x
    rw [heq]
    exact hcover j z
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hcompare] with n hn
  intro j v z hz B hB
  exact finitePartitionCoupling_bad_le_of_cell_error _ _ hm hm hd hd
    (hc j z) (le_of_lt hε) (hn j v z hz) B hB

end LatticeProb.PartitionSelector
