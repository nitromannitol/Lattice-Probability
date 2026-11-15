import LatticeProb.MeasureTheory.FiniteIntervalSuccessor

/-! # Grid points in an interval cover -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- In a finite cover by equal-length intervals with disjoint interiors, every
point of the corresponding grid strictly before the right boundary is the left
endpoint of one of the intervals. -/
theorem exists_interval_at_grid_point
    {ι : Type*} [Finite ι] (c d ℓ : ℝ) (A B : ι → ℝ)
    (hℓ : 0 < ℓ) (hbound : ∀ i, c ≤ A i)
    (hlen : ∀ i, B i - A i = ℓ)
    (hdis : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hcover : Icc c d ⊆ ⋃ i, Icc (A i) (B i))
    (n : ℕ) (hn : c + (n : ℝ) * ℓ < d) :
    ∃ i, A i = c + (n : ℝ) * ℓ := by
  have hne : ∀ i, A i < B i := by
    intro i
    linarith [hlen i]
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero] at hn ⊢
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨le_rfl, hn.le⟩)
    exact ⟨i, le_antisymm hi.1 (hbound i)⟩
  | succ n ih =>
    have hn' : c + (n : ℝ) * ℓ < d := by
      rw [Nat.cast_succ] at hn
      nlinarith
    obtain ⟨i, hi⟩ := ih hn'
    have hB : B i = c + ((n + 1 : ℕ) : ℝ) * ℓ := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith [hlen i]
    obtain ⟨j, _, hj⟩ := exists_interval_successor_of_finite_cover c d A B
      hne hdis hcover i (le_trans (hbound i) (hne i).le) (hB ▸ hn)
    exact ⟨j, hj.trans hB⟩

end LatticeProb
