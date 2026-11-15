import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Grid cells at excursion endpoints -/

set_option autoImplicit false

namespace LatticeProb

/-- Two endpoints strictly inside separated intervals can be placed in mesh cells
whose inner endpoints lie strictly between them. At a grid point the cell is
chosen on the side of the interval between the endpoints. -/
theorem exists_excursion_grid_cells {a b c d s t ε : ℝ}
    (hbc : b < c)
    (hε : 0 < ε) (h₁ : ε < s - a) (h₂ : ε < b - s)
    (h₃ : ε < t - c) (h₄ : ε < d - t) :
    ∃ i j : ℤ, i + 1 < j ∧
      a < ε * ((i : ℝ) - 1) ∧ ε * ((i : ℝ) - 1) ≤ s ∧
      s < ε * i ∧ ε * i < b ∧
      c < ε * ((j : ℝ) - 1) ∧ ε * ((j : ℝ) - 1) < t ∧
      t ≤ ε * j ∧ ε * j < d ∧ ε * i < ε * ((j : ℝ) - 1) := by
  let i : ℤ := ⌊s / ε⌋ + 1
  let j : ℤ := ⌈t / ε⌉
  have hslo := Int.floor_le (s / ε)
  have hshi := Int.lt_floor_add_one (s / ε)
  have htlo := Int.le_ceil (t / ε)
  have hthi := Int.ceil_lt_add_one (t / ε)
  have hslo' : ε * ((i : ℝ) - 1) ≤ s := by
    dsimp [i]
    push_cast
    have := (le_div_iff₀ hε).mp hslo
    nlinarith
  have hshi' : s < ε * i := by
    dsimp [i]
    push_cast
    have := (div_lt_iff₀ hε).mp hshi
    nlinarith
  have htlo' : t ≤ ε * j := by
    dsimp [j]
    have := (div_le_iff₀ hε).mp htlo
    nlinarith
  have hthi' : ε * j < t + ε := by
    dsimp [j]
    have := (lt_div_iff₀ hε).mp (show (⌈t / ε⌉ : ℝ) < (t + ε) / ε by
      rw [add_div, div_self (ne_of_gt hε)]
      exact hthi)
    nlinarith
  have hleft : s - ε < ε * ((i : ℝ) - 1) := by nlinarith
  have hright : ε * ((j : ℝ) - 1) < t := by nlinarith
  have hiup : ε * i ≤ s + ε := by nlinarith
  have hjlow : t - ε ≤ ε * ((j : ℝ) - 1) := by nlinarith
  have hsep : ε * i < ε * ((j : ℝ) - 1) := by linarith
  have hij : i + 1 < j := by
    have : (i : ℝ) + 1 < j := by nlinarith
    exact_mod_cast this
  refine ⟨i, j, hij, ?_, hslo', hshi', ?_, ?_, hright, htlo', ?_, hsep⟩ <;> linarith

end LatticeProb
