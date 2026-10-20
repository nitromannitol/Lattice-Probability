/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedWalk/Basic.lean.
Source: ReflectedWalk/Energy.lean.
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-!
# Conductance graphs and Dirichlet energy with possibly infinite degrees

A conductance graph is a vertex type `V` with a symmetric, nonnegative conductance
`c : V → V → ℝ` that vanishes on the diagonal and is summable in each row. Two vertices are
adjacent when their conductance is positive, and every vertex has finite total conductance
`pi x = ∑' y, c x y`. Vertices may have infinitely many neighbours. Connectedness is not part of
the structure; it is a separate hypothesis `G.toSimpleGraph.Connected` where a theorem needs it.

* `ConductanceGraph`: the structure, and its adjacency, `toSimpleGraph`, and stationary weight
  `pi`. The lemmas `c_le_pi`, `pi_pos_of_adj`, `exists_adj_of_connected`, and
  `pi_pos_of_connected` relate them.
* `gradSq`, `HasFiniteEnergy`, `Energy`: the Dirichlet energy
  `Energy f = (∑' p : V × V, c p.1 p.2 * (f p.2 - f p.1) ^ 2) / 2`. The halved sum over ordered
  pairs is the sum over unoriented edges. When `HasFiniteEnergy f` fails, `Energy f` is the junk
  value `0` (a non-summable `tsum` is `0` in Lean), so comparisons with `Energy` need
  `HasFiniteEnergy` as a hypothesis.
* `abs_sub_le_of_adj`, `walkConst`, `abs_sub_le_walkConst_mul`: the increment of a finite-energy
  function across one edge, and along a walk, is bounded by `√(2 Energy f)` times a constant that
  depends only on the edge or the walk.

The example section at the end checks that the structure is inhabited by a path on three vertices
and by a complete graph on `ℕ` whose vertices all have infinite degree.

## Relation to LP's finite networks

`LatticeProb.Network` (`IsCond`, `netLaplacian`, `formOn`, `energyOn`, and the Dirichlet problem)
works on a `SimpleGraph` with a conductance `IsCond G c`, and most of its results assume
`[G.LocallyFinite]`. The structure here is the summable, possibly infinite-degree model, and its
energy is normalised by `½` over ordered pairs. LP's `energyOn` has no `½`, so on a finite vertex
set it is twice `Energy`. This file does not reprove LP's finite results and does not yet connect
`ConductanceGraph` to `IsCond`.
-/

namespace LatticeProb.Network

/-- A vertex type with edge conductances. Connectedness is not part of this structure; it is
stated separately as `G.toSimpleGraph.Connected` so that intermediate constructions may be
stated without it. -/
structure ConductanceGraph (V : Type*) where
  /-- Conductance of the edge between two vertices; `0` when they are not adjacent. -/
  c : V → V → ℝ
  /-- Conductances live on unoriented edges. -/
  c_symm : ∀ x y, c x y = c y x
  c_nonneg : ∀ x y, 0 ≤ c x y
  /-- No self-loops. -/
  c_self : ∀ x, c x x = 0
  /-- Every row is summable, so the total conductance `pi x` at each vertex is finite. -/
  summable_c : ∀ x, Summable (c x)

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- Adjacency: `x ∼ y` exactly when the conductance between them is positive. -/
def Adj (x y : V) : Prop := 0 < G.c x y

/-- Adjacency is symmetric. -/
theorem adj_symm {x y : V} (h : G.Adj x y) : G.Adj y x := by
  rw [Adj, G.c_symm]; exact h

/-- No vertex is adjacent to itself. -/
theorem adj_irrefl (x : V) : ¬ G.Adj x x := by
  simp [Adj, G.c_self]

/-- The underlying simple graph. Connectedness of `G` means connectedness of this. -/
def toSimpleGraph : SimpleGraph V where
  Adj := G.Adj
  symm := ⟨fun _ _ h => G.adj_symm h⟩
  loopless := ⟨fun x => G.adj_irrefl x⟩

/-- Two vertices are adjacent in `G.toSimpleGraph` exactly when their conductance is positive. -/
@[simp] theorem toSimpleGraph_adj {x y : V} : G.toSimpleGraph.Adj x y ↔ 0 < G.c x y := Iff.rfl

/-- The stationary weight `pi x = ∑_{y ∼ x} c(x,y)` at a vertex. The sum is taken over all of
`V`; non-neighbours contribute `0`. -/
noncomputable def pi (x : V) : ℝ := ∑' y, G.c x y

/-- The total conductance `pi x` at a vertex is nonnegative. -/
theorem pi_nonneg (x : V) : 0 ≤ G.pi x :=
  tsum_nonneg fun y => G.c_nonneg x y

/-- Each conductance at `x` is at most the total conductance `pi x`. -/
theorem c_le_pi (x y : V) : G.c x y ≤ G.pi x :=
  (G.summable_c x).le_tsum y fun b _ => G.c_nonneg x b

/-- A vertex with a neighbour has positive stationary weight. -/
theorem pi_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < G.pi x :=
  lt_of_lt_of_le h (G.c_le_pi x y)

/-- In a connected graph with at least two vertices, every vertex has a neighbour. -/
theorem exists_adj_of_connected (hG : G.toSimpleGraph.Connected) [Nontrivial V] (x : V) :
    ∃ y, G.Adj x y := by
  obtain ⟨z, hz⟩ := exists_ne x
  obtain ⟨w⟩ := hG.preconnected x z
  cases w with
  | nil => exact absurd rfl hz
  | cons h _ => exact ⟨_, h⟩

/-- In a connected graph with at least two vertices, every stationary weight is positive. -/
theorem pi_pos_of_connected (hG : G.toSimpleGraph.Connected) [Nontrivial V] (x : V) :
    0 < G.pi x := by
  obtain ⟨y, hy⟩ := G.exists_adj_of_connected hG x
  exact G.pi_pos_of_adj hy

/-- The contribution of one *ordered* pair `(x, y)` to the Dirichlet energy. -/
noncomputable def gradSq (f : V → ℝ) (p : V × V) : ℝ := G.c p.1 p.2 * (f p.2 - f p.1) ^ 2

/-- Each summand `c x y (f x - f y)^2` of the energy is nonnegative. -/
theorem gradSq_nonneg (f : V → ℝ) (p : V × V) : 0 ≤ G.gradSq f p :=
  mul_nonneg (G.c_nonneg _ _) (sq_nonneg _)

/-- `f` has finite Dirichlet energy: the family of ordered-pair contributions is summable. -/
def HasFiniteEnergy (f : V → ℝ) : Prop := Summable (G.gradSq f)

/-- The Dirichlet energy `∑ c(x,y) (f y - f x) ^ 2` over unoriented edges, written as half the
sum over ordered pairs. It is meaningful only when `HasFiniteEnergy f` holds. -/
noncomputable def Energy (f : V → ℝ) : ℝ := (∑' p : V × V, G.gradSq f p) / 2

/-- The energy is nonnegative. -/
theorem Energy_nonneg (f : V → ℝ) : 0 ≤ G.Energy f := by
  apply div_nonneg _ (by norm_num)
  exact tsum_nonneg fun p => G.gradSq_nonneg f p

/-- The sum of the energy summands over ordered pairs is twice the energy. -/
theorem tsum_gradSq_eq (f : V → ℝ) : ∑' p : V × V, G.gradSq f p = 2 * G.Energy f := by
  rw [Energy]; ring

/-- A single ordered pair contributes at most the whole energy sum. -/
theorem gradSq_le_two_energy {f : V → ℝ} (hf : G.HasFiniteEnergy f) (p : V × V) :
    G.gradSq f p ≤ 2 * G.Energy f := by
  rw [← G.tsum_gradSq_eq f]
  exact hf.le_tsum p fun b _ => G.gradSq_nonneg f b

/-- The single-edge increment bound: across an edge of conductance `c x y > 0`, a finite-energy
function changes by at most `√(2 Energy f) / √(c x y)`. -/
theorem abs_sub_le_of_adj {f : V → ℝ} (hf : G.HasFiniteEnergy f) {x y : V}
    (hxy : G.Adj x y) :
    |f y - f x| ≤ Real.sqrt (2 * G.Energy f) / Real.sqrt (G.c x y) := by
  have hc : 0 < G.c x y := hxy
  have hkey : G.c x y * (f y - f x) ^ 2 ≤ 2 * G.Energy f :=
    G.gradSq_le_two_energy hf (x, y)
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hc)]
  have h1 : |f y - f x| * Real.sqrt (G.c x y) =
      Real.sqrt ((f y - f x) ^ 2 * G.c x y) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rw [h1]
  apply Real.sqrt_le_sqrt
  rw [mul_comm ((f y - f x) ^ 2)]
  exact hkey

section WalkConst

open SimpleGraph

/-- The constant `∑_j 1/√(c_j)` accumulated along a walk. It depends only on the walk, not on
the function being estimated. -/
noncomputable def walkConst : {a b : V} → G.toSimpleGraph.Walk a b → ℝ
  | _, _, Walk.nil => 0
  | a, _, Walk.cons (v := v) _ p => 1 / Real.sqrt (G.c a v) + walkConst p

/-- The walk constant of every walk is nonnegative. -/
theorem walkConst_nonneg : ∀ {a b : V} (w : G.toSimpleGraph.Walk a b), 0 ≤ G.walkConst w
  | _, _, Walk.nil => le_refl 0
  | a, _, Walk.cons (v := v) _ p => by
      have h1 : (0:ℝ) ≤ 1 / Real.sqrt (G.c a v) := by positivity
      exact add_nonneg h1 (walkConst_nonneg p)

/-- **Key estimate.** Along any walk from `a` to `b`, the increment of a finite-energy function
is at most `walkConst` times `√(2 · Energy f)`. Each edge is bounded separately rather than by
Cauchy–Schwarz along the whole walk, so the constant is not optimal. -/
theorem abs_sub_le_walkConst_mul {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    ∀ {a b : V} (w : G.toSimpleGraph.Walk a b),
      |f b - f a| ≤ G.walkConst w * Real.sqrt (2 * G.Energy f)
  | _, _, Walk.nil => by simp [walkConst]
  | a, b, Walk.cons (v := v) h p => by
      have hstep : |f v - f a| ≤ Real.sqrt (2 * G.Energy f) / Real.sqrt (G.c a v) :=
        G.abs_sub_le_of_adj hf h
      have hrest : |f b - f v| ≤ G.walkConst p * Real.sqrt (2 * G.Energy f) :=
        abs_sub_le_walkConst_mul hf p
      have htri : |f b - f a| ≤ |f v - f a| + |f b - f v| := by
        have : f b - f a = (f v - f a) + (f b - f v) := by ring
        rw [this]; exact abs_add_le _ _
      refine htri.trans (le_of_le_of_eq (add_le_add hstep hrest) ?_)
      rw [walkConst]
      ring

end WalkConst

end ConductanceGraph

/-! ## Examples

These show that the hypotheses of `ConductanceGraph` are not contradictory: one example with
finitely many vertices and one in which every vertex has infinite degree. -/

namespace ConductanceGraph.Example

/-- The path `0 – 1 – 2` on `Fin 3`, with unit conductance on its two edges. -/
def path3 : ConductanceGraph (Fin 3) where
  c x y := if x.val + 1 = y.val ∨ y.val + 1 = x.val then 1 else 0
  c_symm x y := by simp only [or_comm]
  c_nonneg x y := by split_ifs <;> norm_num
  c_self x := by simp
  summable_c x := Summable.of_finite

/-- In `path3`, the vertices `0` and `1` are adjacent and `0` and `2` are not. -/
example : path3.Adj 0 1 ∧ ¬ path3.Adj 0 2 := by
  norm_num [ConductanceGraph.Adj, path3]

/-- The complete graph on `ℕ` with conductance `2 ^ (-(x + y))` between distinct vertices. Every
row is summable, while each vertex has infinitely many neighbours. -/
noncomputable def halfPowGraph : ConductanceGraph ℕ where
  c x y := if x = y then 0 else (1 / 2 : ℝ) ^ (x + y)
  c_symm x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h, add_comm]
  c_nonneg x y := by split_ifs <;> positivity
  c_self x := by simp
  summable_c x := by
    refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_)
      (summable_geometric_two.mul_left ((1 / 2 : ℝ) ^ x))
    · split_ifs <;> positivity
    · rw [pow_add]; split_ifs <;> first | positivity | exact le_rfl

/-- In `halfPowGraph`, vertex `0` is adjacent to every vertex `n + 1`. -/
example : ∀ n : ℕ, halfPowGraph.Adj 0 (n + 1) := by
  intro n
  norm_num [ConductanceGraph.Adj, halfPowGraph]

end ConductanceGraph.Example

end LatticeProb.Network
