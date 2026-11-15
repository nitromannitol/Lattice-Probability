import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! A bounded interval as complete cells and one short remainder. -/

open Set

namespace LatticeProb

/-- Consecutive half-open intervals of a fixed nonnegative length partition
an interval of an integer multiple of that length. -/
theorem Ico_eq_biUnion_cells (u h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    Ico u (u + (n : ℝ) * h) =
      ⋃ i ∈ Finset.range n, Ico (u + (i : ℝ) * h) (u + ((i : ℝ) + 1) * h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ : u ≤ u + (n : ℝ) * h := by
      have hn : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
      linarith
    have h₂ : u + (n : ℝ) * h ≤ u + ((n : ℝ) + 1) * h := by nlinarith
    rw [Nat.cast_succ, ← Ico_union_Ico_eq_Ico h₁ h₂, ih,
      Finset.range_add_one]
    simp only [Finset.set_biUnion_insert]
    rw [union_comm]

/-- The greatest complete-cell endpoint leaves a remainder shorter than one cell. -/
theorem exists_cell_endpoint (u v h : ℝ) (huv : u ≤ v) (hh : 0 < h) :
    ∃ n : ℕ, u ≤ u + (n : ℝ) * h ∧
      u + (n : ℝ) * h ≤ v ∧ v < u + (n : ℝ) * h + h := by
  let n := ⌊(v - u) / h⌋₊
  have hd : 0 ≤ (v - u) / h := div_nonneg (sub_nonneg.mpr huv) hh.le
  have hlo : (n : ℝ) ≤ (v - u) / h := Nat.floor_le hd
  have hhi : (v - u) / h < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo' := (le_div_iff₀ hh).mp hlo
  have hhi' := (div_lt_iff₀ hh).mp hhi
  refine ⟨n, ?_, ?_, ?_⟩
  · have hn : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    linarith
  · linarith
  · nlinarith

/-- Two ordered half-open cells are disjoint. -/
theorem disjoint_Ico_cells (u h : ℝ) (hh : 0 ≤ h) {i j : ℕ} (hij : i < j) :
    Disjoint (Ico (u + (i : ℝ) * h) (u + ((i : ℝ) + 1) * h))
      (Ico (u + (j : ℝ) * h) (u + ((j : ℝ) + 1) * h)) := by
  have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have hmul := mul_le_mul_of_nonneg_right hij' hh
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [mem_Ico] at hx hy
  nlinarith

/-- An interval is the union of complete cells and a remainder shorter than
one cell, with cells measured from its left endpoint. -/
theorem exists_Ico_cell_partition (u v h : ℝ) (huv : u ≤ v) (hh : 0 < h) :
    ∃ n : ℕ, u + (n : ℝ) * h ≤ v ∧ v < u + (n : ℝ) * h + h ∧
      Ico u v = (⋃ i ∈ Finset.range n,
        Ico (u + (i : ℝ) * h) (u + ((i : ℝ) + 1) * h)) ∪
        Ico (u + (n : ℝ) * h) v := by
  obtain ⟨n, h₁, h₂, h₃⟩ := exists_cell_endpoint u v h huv hh
  refine ⟨n, h₂, h₃, ?_⟩
  rw [← Ico_eq_biUnion_cells u h hh.le n, Ico_union_Ico_eq_Ico h₁ h₂]

end LatticeProb
