module

/-
Coordinate bounds along nearest-neighbour walks in `ℤ^d`.

Adjacent sites of `lattice d` differ by at most one in each coordinate.  Along a walk
`z 0, z 1, …, z (m - 1)` of consecutive adjacent sites, the `c`-th coordinate of `z i`
differs from that of `z 0` by at most `i`.  Hence a site whose every coordinate lies in the
range of that coordinate along the walk has coordinate-sum distance at most `d (m - 1)`
from `z 0`.  The statements use plain sums of absolute coordinate differences.
-/
public import Mathlib
public import LatticeProb.Site

@[expose] public section

namespace LatticeProb

/-- A unit vector has every coordinate of absolute value at most one. -/
private theorem abs_unit_coord_le_one {d : ℕ} (i c : Fin d) : |unit i c| ≤ 1 := by
  unfold unit
  rw [Pi.single_apply]
  split_ifs <;> simp

/-- Adjacent sites differ by at most one in each coordinate. -/
theorem abs_sub_coord_le_one_of_adj {d : ℕ} {x y : Site d} (h : (lattice d).Adj x y)
    (c : Fin d) : |x c - y c| ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi, Pi.add_apply, show x c - (x c + unit i c) = -unit i c by ring, abs_neg]
    exact abs_unit_coord_le_one i c
  · rw [hi, Pi.add_apply, show y c + unit i c - y c = unit i c by ring]
    exact abs_unit_coord_le_one i c

/-- Along a walk of consecutive adjacent sites, the `c`-th coordinate of the `i`-th site
differs from that of the first site by at most `i`. -/
theorem abs_sub_coord_le_of_walk {d : ℕ} (z : ℕ → Site d) (m : ℕ)
    (hadj : ∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) (c : Fin d) :
    ∀ i, i < m → |z i c - z 0 c| ≤ (i : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 : |z (i + 1) c - z i c| ≤ 1 := by
      rw [abs_sub_comm]
      exact abs_sub_coord_le_one_of_adj (hadj i hi) c
    have h3 := abs_sub_le (z (i + 1) c) (z i c) (z 0 c)
    push_cast
    linarith

/-- A site whose every coordinate lies in the range of that coordinate along a walk of
consecutive adjacent sites is within coordinate-sum distance `d (m - 1)` of the first site
of the walk. -/
theorem sum_abs_sub_le_of_walk_box {d : ℕ} (z : ℕ → Site d) (m : ℕ)
    (hadj : ∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) (x : Site d)
    (hx : ∀ c : Fin d, (∃ i, i < m ∧ z i c ≤ x c) ∧ (∃ i, i < m ∧ x c ≤ z i c)) :
    ∑ c, |x c - z 0 c| ≤ (d : ℤ) * ((m : ℤ) - 1) := by
  have hcoord : ∀ c : Fin d, |x c - z 0 c| ≤ (m : ℤ) - 1 := by
    intro c
    obtain ⟨⟨i, hi, hzi⟩, ⟨i', hi', hxi⟩⟩ := hx c
    have h1 := abs_le.mp (abs_sub_coord_le_of_walk z m hadj c i hi)
    have h2 := abs_le.mp (abs_sub_coord_le_of_walk z m hadj c i' hi')
    have h3 : (i : ℤ) ≤ (m : ℤ) - 1 := by omega
    have h4 : (i' : ℤ) ≤ (m : ℤ) - 1 := by omega
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc ∑ c, |x c - z 0 c| ≤ ∑ _c : Fin d, ((m : ℤ) - 1) :=
        Finset.sum_le_sum fun c _ => hcoord c
    _ = (d : ℤ) * ((m : ℤ) - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end LatticeProb
