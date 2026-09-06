/-
Paths on the lattice: a step is a signed coordinate direction, a path is a word
of steps, and the position after `k` steps is the partial sum of the word.

The `2d` unit steps are named by `Dir d = Fin d × Bool`, a coordinate together
with a sign, rather than by the `2d` sites `± e_i`, so that summing over the
neighbours of a site is a sum over a fixed type and `d = 0` needs no special
case.  `dirVec` sends a direction to the unit vector it names, and
`dirVec_eq_unit` identifies those vectors with the `unit i` of
`LatticeProb.Site`.

A path of length `n` is a word `w : Fin n → Dir d`, read as a walk started at
the origin.  `pos w k` is its position after `k` steps, constant once `k`
reaches `n`; `pathRange w k` is the set of sites visited up to time `k` and
`pathEdges w k` the set of undirected edges crossed.
-/
import LatticeProb.Site

namespace LatticeProb

open Finset

/-- A direction: a coordinate together with a sign.  There are `2d` of them. -/
abbrev Dir (d : ℕ) := Fin d × Bool

/-- The unit vector `± e_i` named by a direction. -/
def dirVec {d : ℕ} (a : Dir d) : Site d :=
  fun j => if j = a.1 then (if a.2 then 1 else -1) else 0

/-- The positive directions are the unit vectors of `LatticeProb.Site`. -/
theorem dirVec_eq_unit {d : ℕ} (i : Fin d) : dirVec ((i, true) : Dir d) = unit i := by
  funext j
  by_cases h : j = i <;> simp [dirVec, unit, h]

/-- The negative directions are the negated unit vectors. -/
theorem dirVec_eq_neg_unit {d : ℕ} (i : Fin d) : dirVec ((i, false) : Dir d) = -unit i := by
  funext j
  by_cases h : j = i <;> simp [dirVec, unit, h]

/-- Position after `k` steps of the direction word `w`; the walk starts at the
origin, and `pos` is constant once `k` reaches the length of the word. -/
def pos {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Site d :=
  ∑ i : Fin n, if (i : ℕ) < k then dirVec (w i) else 0

/-- The undirected edge crossed by step `i + 1`. -/
def edgeAt {d n : ℕ} (w : Fin n → Dir d) (i : ℕ) : Sym2 (Site d) :=
  s(pos w i, pos w (i + 1))

/-- The set of undirected edges crossed in the first `k` steps; empty at `k = 0`.

The `min k n` matters.  `edgeAt w i` for `i ≥ n` is the degenerate loop
`s(pos w n, pos w n)`, which a path of length `n` never crosses; without the
`min`, the bound `|pathEdges| ≤ d |pathRange|` is false.  For `k ≤ n`, which is
the only range a step rule ever uses, `min k n = k`. -/
def pathEdges {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Finset (Sym2 (Site d)) :=
  (range (min k n)).image (edgeAt w)

/-- The set of sites visited up to time `k`. -/
def pathRange {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Finset (Site d) :=
  (range (k + 1)).image (pos w)

/-- A sum over the neighbours of `x` in the sense of `LatticeProb.nbrSum` is a
sum over the `2d` directions. -/
theorem nbrSum_eq_sum_dir {d : ℕ} (u : Site d → ℝ) (x : Site d) :
    nbrSum u x = ∑ a : Dir d, u (x + dirVec a) := by
  rw [nbrSum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, dirVec_eq_unit, dirVec_eq_neg_unit, ← sub_eq_add_neg]

/-- The simple random walk operator averages over the `2d` directions. -/
theorem walkOp_eq_sum_dir {d : ℕ} (u : Site d → ℝ) (x : Site d) :
    walkOp u x = (∑ a : Dir d, u (x + dirVec a)) / (2 * d) := by
  rw [walkOp, nbrSum_eq_sum_dir]

end LatticeProb
