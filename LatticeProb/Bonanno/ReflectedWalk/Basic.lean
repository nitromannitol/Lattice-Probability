/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Basic at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Conductance graphs (Gwynne–Sung, Section 1.1)

The standing setup of arXiv:2506.18827: a countably infinite connected graph
`G = (VG, EG, c)` with conductances `c : EG → (0,∞)` and stationary measure

  `π(x) = ∑_{y ∼ x} c(x,y) < ∞`,   (1.1)–(1.2)

where `G` is **not** assumed locally finite.

## Representation

Conductances are carried as a symmetric function `c : V → V → ℝ` that vanishes on
the diagonal, is nonnegative, and is summable in the second variable.  Adjacency is
*derived*: `x ∼ y ↔ 0 < c x y`.  This packages `EG` and `c` in one object and makes
`π` a `tsum` over all of `V`, which is the form every later estimate uses.

Summability of `c x` is exactly the paper's (1.2): the paper writes `π(x) < ∞` for a
sum of nonnegative terms, and for nonnegative families summability and finiteness of
the sum agree.  Vertices of infinite degree are allowed.
-/

namespace ReflectedWalk

/-- A countable graph equipped with edge conductances, in the sense of
Gwynne–Sung Section 1.1.  Connectedness is *not* part of this structure; it is
carried separately as `G.toSimpleGraph.Connected` so that intermediate
constructions may be stated without it. -/
structure ConductanceGraph (V : Type*) where
  /-- Conductance of the edge between two vertices; `0` when they are not adjacent. -/
  c : V → V → ℝ
  /-- Conductances live on unoriented edges. -/
  c_symm : ∀ x y, c x y = c y x
  c_nonneg : ∀ x y, 0 ≤ c x y
  /-- No self-loops. -/
  c_self : ∀ x, c x x = 0
  /-- The paper's (1.2): `π(x) < ∞` for every vertex. -/
  summable_c : ∀ x, Summable (c x)

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- Adjacency: `x ∼ y` exactly when the conductance between them is positive. -/
def Adj (x y : V) : Prop := 0 < G.c x y

lemma adj_symm {x y : V} (h : G.Adj x y) : G.Adj y x := by
  rw [Adj, G.c_symm]; exact h

lemma adj_irrefl (x : V) : ¬ G.Adj x x := by
  simp [Adj, G.c_self]

/-- The underlying simple graph.  Connectedness of `G` means connectedness of this. -/
def toSimpleGraph : SimpleGraph V where
  Adj := G.Adj
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun x => G.adj_irrefl x⟩

@[simp] lemma toSimpleGraph_adj {x y : V} : G.toSimpleGraph.Adj x y ↔ 0 < G.c x y := Iff.rfl

/-- The stationary measure `π(x) = ∑_{y ∼ x} c(x,y)` of (1.1).  The sum is taken
over all of `V`; non-neighbours contribute `0`. -/
noncomputable def pi (x : V) : ℝ := ∑' y, G.c x y

lemma pi_nonneg (x : V) : 0 ≤ G.pi x :=
  tsum_nonneg fun y => G.c_nonneg x y

lemma c_le_pi (x y : V) : G.c x y ≤ G.pi x :=
  (G.summable_c x).le_tsum y fun b _ => G.c_nonneg x b

/-- A vertex with a neighbour has positive stationary measure. -/
lemma pi_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < G.pi x :=
  lt_of_lt_of_le h (G.c_le_pi x y)

/-- In a connected graph with at least two vertices, every vertex has a neighbour. -/
lemma exists_adj_of_connected (hG : G.toSimpleGraph.Connected) [Nontrivial V] (x : V) :
    ∃ y, G.Adj x y := by
  obtain ⟨z, hz⟩ := exists_ne x
  obtain ⟨w⟩ := hG.preconnected x z
  cases w with
  | nil => exact absurd rfl hz
  | cons h _ => exact ⟨_, h⟩

lemma pi_pos_of_connected (hG : G.toSimpleGraph.Connected) [Nontrivial V] (x : V) :
    0 < G.pi x := by
  obtain ⟨y, hy⟩ := G.exists_adj_of_connected hG x
  exact G.pi_pos_of_adj hy

end ConductanceGraph

end ReflectedWalk
