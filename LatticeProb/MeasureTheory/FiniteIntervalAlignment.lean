import LatticeProb.MeasureTheory.FiniteIntervalGrid
import LatticeProb.Analysis.IntervalCellPartition

/-! # Alignment in an interval cover -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- In a finite equal-length cover by intervals with disjoint interiors,
every interval contained in the covered range starts at a grid point. -/
theorem interval_left_endpoint_eq_grid_point
    {ι : Type*} [Finite ι] (c d ℓ : ℝ) (A B : ι → ℝ)
    (hℓ : 0 < ℓ) (hbound : ∀ i, c ≤ A i)
    (hlen : ∀ i, B i - A i = ℓ)
    (hdis : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hcover : Icc c d ⊆ ⋃ i, Icc (A i) (B i))
    (i : ι) (hi : B i ≤ d) :
    ∃ n : ℕ, A i = c + (n : ℝ) * ℓ := by
  obtain ⟨n, _, hn, hn'⟩ := exists_cell_endpoint c (A i) ℓ (hbound i) hℓ
  have hid : A i < d := by linarith [hlen i]
  obtain ⟨j, hj⟩ := exists_interval_at_grid_point c d ℓ A B hℓ hbound hlen hdis hcover n
    (lt_of_le_of_lt hn hid)
  refine ⟨n, le_antisymm ?_ hn⟩
  by_contra h
  have hlt : c + (n : ℝ) * ℓ < A i := lt_of_not_ge h
  have hij : i ≠ j := by
    intro heq
    subst j
    linarith
  have hBj : B j = c + (n : ℝ) * ℓ + ℓ := by linarith [hlen j]
  have hiB : A i < B i := by linarith [hlen i]
  have hjB : A j < B j := by linarith [hlen j]
  have hord := (Ioo_disjoint_Ioo).mp (hdis hij)
  simp only [min_le_iff, le_max_iff] at hord
  rcases hord with (h | h) | (h | h) <;> linarith

end LatticeProb
