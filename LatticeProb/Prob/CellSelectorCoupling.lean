import LatticeProb.Prob.UniformCellCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! # Coupled cell selectors and endpoint proximity -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace LatticeProb

/-- A finite partition coupling controls both disagreement of a selector
constructed from the partition and separation beyond the cell diameter. -/
theorem finite_uniform_nearby_partition_coupling_selector_error_le
    {d : ℕ} {J : Type*} [Fintype J]
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    {ι A : Type*} [Fintype ι] (S : ι → Set (Euc d)) (select : ι → Option A)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (S i)) = 0)
    (hcover : ∀ j z, (ν j z : Measure (Euc d)) (⋃ i, S i) = 1)
    (r : ℝ) (hdiam : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, dist x y < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
      dist (p j n v) z ≤ δ →
        finitePartitionCoupling (μ j n v : Measure (Euc d))
          (ν j z : Measure (Euc d)) S S
          {q | cellSelector S select q.1 ≠ cellSelector S select q.2 ∨
            r ≤ dist q.1 q.2} ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  obtain ⟨δ, hδ, hbound⟩ :=
    finite_uniform_nearby_partition_coupling_bad_le P V p μ ν hν hLP S hS hdisj
      hnull hcover hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j v z hz
  apply hn j v z hz
  intro i
  apply Set.disjoint_left.mpr
  intro q hbad hq
  have hx := (cellLabel_eq_some_iff S hdisj q.1 i).mpr hq.1
  have hy := (cellLabel_eq_some_iff S hdisj q.2 i).mpr hq.2
  rcases hbad with hne | hfar
  · exact hne ((cellSelector_of_label S select hx).trans
      (cellSelector_of_label S select hy).symm)
  · exact (not_le_of_gt (hdiam i q.1 hq.1 q.2 hq.2)) hfar

end LatticeProb
