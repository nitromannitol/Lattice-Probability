/-
The vertex boundary of a set in a graph, moved from `Exploding-Sandpiles`'s
`Exploding/Support/Vocab.lean:17-26`, generalized from the nearest-neighbour
lattice `LatticeProb.lattice d` to an arbitrary `SimpleGraph V` (the source's
own definitions never use the lattice structure, only adjacency).

The same vocabulary was independently written a second time, for `ℤ^d` only,
in `Random-Abelian-Sandpile`'s `RandomSandpile/Support/Basic.lean:164-172` as
`boundary`/`closure`; that repo's `boundary A = {y | y ∉ A ∧ ∃ x ∈ A, Adj y x}`
and `closure A = A ∪ boundary A` are exactly `LatticeProb.Graph.outerBoundary`
and `LatticeProb.Graph.closureN` at `G = LatticeProb.lattice d`, so once this
module is available `RandomSandpile` can drop its own copies and import these
instead.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace LatticeProb.Graph

variable {V : Type*}

/-- The outer boundary `∂A`: the vertices outside `A` adjacent to a vertex of
`A`. -/
def outerBoundary (G : SimpleGraph V) (A : Set V) : Set V :=
  {x | x ∉ A ∧ ∃ y ∈ A, G.Adj x y}

/-- The closure `Ā = A ∪ ∂A`. -/
def closureN (G : SimpleGraph V) (A : Set V) : Set V := A ∪ outerBoundary G A

/-- The inner boundary `∂°A`: the vertices of `A` adjacent to a vertex outside
`A`. -/
def innerBoundary (G : SimpleGraph V) (A : Set V) : Set V :=
  {x | x ∈ A ∧ ∃ y, y ∉ A ∧ G.Adj x y}

end LatticeProb.Graph
