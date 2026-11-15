import LatticeProb.Analysis.ClockedCellIntervalMinima

/-! # Strict comparisons of clocked cell interval minima -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- For a countable family of contours, weak cell-to-middle comparisons are
strict outside a countable set of phases, simultaneously for all nonconsecutive
integer cells. -/
theorem countable_clocked_cell_interval_strict_failures
    {ι : Type*} [Countable ι] (f : ι → ℝ → ℝ)
    (hf : ∀ k, Continuous (f k)) (ψ : ℝ ≃o ℝ) (ε : ℝ) (hε : 0 < ε)
    (hdist : ∀ k x y, x ≠ y → IsLocalMin (f k) x → IsLocalMin (f k) y →
      f k x ≠ f k y) :
    {θ : ℝ | ∃ (k : ι) (i j : ℤ), i + 1 < j ∧
      let a := ψ (ε * ((i : ℝ) - 1 + θ))
      let b := ψ (ε * ((i : ℝ) + θ))
      let c := ψ (ε * ((j : ℝ) - 1 + θ))
      let d := ψ (ε * ((j : ℝ) + θ))
      let l := sInf (f k '' Icc a b)
      let m := sInf (f k '' Icc b c)
      let r := sInf (f k '' Icc c d)
      max l r ≤ m ∧ ¬ max l r < m}.Countable := by
  classical
  have hc := countable_iUnion fun k =>
    countable_clocked_cell_interval_minima_all (f k) (hf k) ψ ε hε (hdist k)
  apply hc.mono
  intro θ hθ
  obtain ⟨k, i, j, hij, hle, hnot⟩ := hθ
  apply mem_iUnion.mpr
  refine ⟨k, i, j, hij, ?_⟩
  have heq := le_antisymm hle (le_of_not_gt hnot)
  rcases le_total
      (sInf (f k '' Icc (ψ (ε * ((i : ℝ) - 1 + θ)))
        (ψ (ε * ((i : ℝ) + θ)))))
      (sInf (f k '' Icc (ψ (ε * ((j : ℝ) - 1 + θ)))
        (ψ (ε * ((j : ℝ) + θ))))) with h | h
  · right
    rw [max_eq_right h] at heq
    exact heq.symm
  · left
    rw [max_eq_left h] at heq
    exact heq

end LatticeProb
