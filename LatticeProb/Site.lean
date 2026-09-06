/-
The lattice `ℤ^d`: sites, unit vectors, the nearest-neighbour graph, and the
simple random walk operator.  Shared by every formalization in this library.

How the objects are modelled:

- A site is `Fin d → ℤ`.  Two sites are neighbours when they differ by a unit
  vector; the graph is `lattice d`.
- `nbrSum u x` is the sum of `u` over the `2d` neighbours of `x`, counted with
  multiplicity in the direction `i`, so that `d = 0` is not special-cased.
- `walkOp` is the transition operator of simple random walk,
  `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`.
-/
import Mathlib

namespace LatticeProb

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)
    · exact unit_ne_zero i (by have := congrArg (· - x) hi; simpa using this.symm)⟩

/-- The `2d` neighbours of `x`, as a finset. -/
def nbrFinset {d : ℕ} (x : Site d) : Finset (Site d) :=
  Finset.univ.biUnion fun i : Fin d => {x + unit i, x - unit i}

/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The simple random walk operator `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`. -/
noncomputable def walkOp {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum u x / (2 * d)

/-- The sup-norm box `[-r, r]^d`. -/
def box (d : ℕ) (r : ℕ) : Set (Site d) := {x | ∀ i, |x i| ≤ r}

/-- The vertices joined to `x` inside `S`, along edges of the lattice. -/
def componentIn {d : ℕ} (S : Set (Site d)) (x : Site d) : Set (Site d) :=
  {y | ∃ (hx : x ∈ S) (hy : y ∈ S), ((lattice d).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- `S` contains an infinite nearest-neighbour component. -/
def HasInfiniteComponent {d : ℕ} (S : Set (Site d)) : Prop :=
  ∃ x ∈ S, (componentIn S x).Infinite

end LatticeProb
