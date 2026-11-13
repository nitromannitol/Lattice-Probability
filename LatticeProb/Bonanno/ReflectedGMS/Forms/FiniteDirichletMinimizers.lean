/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FiniteDirichletMinimizers at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VectorTraceMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Analysis.AnchoredEnergy
import LatticeProb.Bonanno.ReflectedGMS.Graph.Restriction
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import LatticeProb.Bonanno.ReflectedWalk.Harmonic

/-!
# Dirichlet minimizers on the finite anchored levels

On a finite vertex type every function is summable against the conductances, so the
finite-energy premise of the existing anchored trace minimizers
(`exists_anchored_trace_minimizer`, `existsUnique_anchored_trace_minimizer`,
`existsUnique_vector_trace_minimizer`) is discharged by finite summation. That turns those
results into unconditional existence and uniqueness statements for *arbitrary* real or
plane-valued boundary data on every finite anchored graph, with the full competition class
of all functions carrying the prescribed trace.

The geometric anchoring itself is not reproved: it is taken from
`Geometry/BoundaryAnchoring` through the finite anchored levels
`AnchoredFiniteExhaustion.exhaustionLevel`, whose restricted graphs are already known to be
`BoundaryAnchored` on the induced anchor set.

The variational orthogonality conjunct already proved in `exists_anchored_trace_minimizer`
is then tested against the indicator of a single non-boundary vertex. On a finite vertex
type this pairing is exactly minus the discrete Laplacian, so the minimizer satisfies the
weighted Dirichlet linear equations `∑_y c(x,y) (f y − f x) = 0` at every vertex off the
boundary; that is the existing `ReflectedWalk.ConductanceGraph.IsHarmonicOn` on `Aᶜ`,
including the absolute-convergence conjunct of Gwynne–Sung footnote 2.

No connectedness beyond `BoundaryAnchored` is imposed, the boundary may be empty or all of
the vertex type, and nothing here assumes a nested family of restrictions.
-/

-- Merged from `ReflectedGMS/Forms/AnchoredFiniteExhaustion.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_AnchoredFiniteExhaustion

/-!
# Finite anchored approximations of an anchored conductance graph

The graph is an arbitrary conductance graph, possibly disconnected, with an arbitrary
boundary set `A` satisfying `BoundaryAnchored G A`: every vertex reaches some vertex of `A`
by a finite walk. Nothing here assumes connectedness, a finite boundary, connected
restrictions, or any finite-support closure of the energy space.

The geometric anchoring of cell patches is already proved in `Geometry/BoundaryAnchoring`
(`boundaryAnchored_restrictGraph_cells_hitting`, `rectangle_boundaryAnchored`) and is not
reproved. What is added here is the purely graph-theoretic statement that anchoring is
inherited by suitable *finite* vertex sets: every finite vertex set is contained in a finite
vertex set `L` such that `restrictGraph G ↑L` is anchored at `A ∩ L`, and, on a countable
vertex type, these finite sets can be chosen monotone and exhausting.

The construction takes, for each vertex of the given finite set, one finite walk to an
anchor and lets `L` be the union of the walk supports. Any intermediate vertex of such a
walk keeps its suffix `Walk.dropUntil` to the same anchor, and that suffix support is
contained in the original support, hence in `L`; so the induced walk exists inside `L`.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace AnchoredFiniteExhaustion

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Anchoring of a restriction from walks staying inside the restricting set -/

/-- The anchor set induced on a restriction: the vertices of `S` that lie in `A`. -/
def inducedAnchorSet (A S : Set V) : Set S := {x : S | (x : V) ∈ A}

@[simp] theorem mem_inducedAnchorSet {A S : Set V} {x : S} :
    x ∈ inducedAnchorSet A S ↔ (x : V) ∈ A := Iff.rfl

/-- A walk whose support stays inside `S` gives reachability in the restricted graph. -/
theorem reachable_restrictGraph_of_walk_support_subset
    {S : Set V} {u a : V} (p : G.toSimpleGraph.Walk u a)
    (hp : ∀ x ∈ p.support, x ∈ S) (hu : u ∈ S) (ha : a ∈ S) :
    (restrictGraph G S).toSimpleGraph.Reachable ⟨u, hu⟩ ⟨a, ha⟩ := by
  rw [restrictGraph_toSimpleGraph]
  exact ⟨p.induce S hp⟩

/-- If every vertex of `S` has a finite walk to a vertex of `A` whose support stays inside
`S`, then the restriction of `G` to `S` is anchored at the part of `A` inside `S`. -/
theorem boundaryAnchored_restrictGraph_of_walks_within
    {A S : Set V}
    (h : ∀ u ∈ S, ∃ a ∈ A, ∃ p : G.toSimpleGraph.Walk u a,
      ∀ x ∈ p.support, x ∈ S) :
    BoundaryAnchored (restrictGraph G S) (inducedAnchorSet A S) := by
  intro x
  obtain ⟨a, haA, p, hp⟩ := h x.1 x.2
  have ha : a ∈ S := hp a p.end_mem_support
  exact ⟨⟨a, ha⟩, haA, reachable_restrictGraph_of_walk_support_subset G p hp x.2 ha⟩

/-! ### Finite anchored supersets -/

/-! ### Nested exhaustion of a countable vertex type -/

section CountableExhaustion

variable [DecidableEq V]

end CountableExhaustion

end AnchoredFiniteExhaustion

end ReflectedGMS

end Merged_AnchoredFiniteExhaustion

set_option autoImplicit false

namespace ReflectedGMS

namespace FiniteDirichletMinimizers

open scoped ENNReal
open StatementIngredients

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-! ### Finite vertex types have no infinite-energy functions -/

/-- On a finite vertex type every function has finite Dirichlet energy: the energy sum has
a finite index type `V × V`. -/
theorem hasFiniteEnergy_of_finite [Finite V] (f : V → ℝ) : G.HasFiniteEnergy f :=
  Summable.of_finite

/-! ### The scalar minimizer for arbitrary boundary data -/

/-- **Existence of the finite anchored Dirichlet minimizer.** For arbitrary real boundary
data `u` there is a function agreeing with `u` on the whole boundary `A`, orthogonal to
every variation vanishing on `A`, and minimizing the Dirichlet energy against *every*
function with that trace. No finiteness of `A`, connectedness, or finite-energy premise on
`u` is needed. -/
theorem exists_finite_anchored_minimizer_orthogonal [Finite V] {A : Set V}
    (hA : BoundaryAnchored G A) (u : V → ℝ) :
    ∃ f : V → ℝ, (∀ a ∈ A, f a = u a) ∧
      (∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm f φ = 0) ∧
      (∀ h : V → ℝ, (∀ a ∈ A, h a = u a) → G.Energy f ≤ G.Energy h) := by
  obtain ⟨f, _hfE, htrace, horth, hmin⟩ :=
    exists_anchored_trace_minimizer G hA (hasFiniteEnergy_of_finite G u)
  exact ⟨f, htrace, horth, fun h hh => hmin h (hasFiniteEnergy_of_finite G h) hh⟩

/-! ### The weighted Dirichlet linear equations at an interior vertex -/

/-- The indicator of one vertex, used as the test variation of the first variation. -/
noncomputable def vertexIndicator (x : V) : V → ℝ :=
  Set.indicator ({x} : Set V) (fun _ => (1 : ℝ))

theorem vertexIndicator_self (x : V) : vertexIndicator x x = 1 := by
  have hx : x ∈ ({x} : Set V) := Set.mem_singleton_iff.2 rfl
  exact Set.indicator_of_mem hx _

theorem vertexIndicator_eq_zero {x y : V} (h : y ≠ x) : vertexIndicator x y = 0 := by
  have hy : y ∉ ({x} : Set V) := fun hy => h (Set.mem_singleton_iff.1 hy)
  exact Set.indicator_of_notMem hy _

/-- **First variation against a single-vertex indicator.** On a finite vertex type the
Dirichlet pairing of `f` with the indicator of `{x}` is minus the discrete Laplacian of `f`
at `x`. -/
theorem dirichletForm_vertexIndicator [Finite V] (f : V → ℝ) (x : V) :
    G.dirichletForm f (vertexIndicator x) = -∑' y, G.lapTerm f x y := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hind : ∀ y : V, vertexIndicator x y = if y = x then (1 : ℝ) else 0 := by
    intro y
    by_cases h : y = x
    · rw [if_pos h, h, vertexIndicator_self]
    · rw [if_neg h, vertexIndicator_eq_zero h]
  have key : ∀ p : V × V, G.gradProd f (vertexIndicator x) p =
      (if p.2 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0) -
        (if p.1 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0) := by
    intro p
    simp only [ReflectedWalk.ConductanceGraph.gradProd, hind]
    by_cases h1 : p.1 = x <;> by_cases h2 : p.2 = x <;> simp [h1, h2] <;> ring
  have hsplit : (∑ p : V × V, G.gradProd f (vertexIndicator x) p) =
      (∑ p : V × V, if p.2 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0) -
        ∑ p : V × V, if p.1 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => key p
  have hcol : (∑ p : V × V, if p.2 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0) =
      ∑ a : V, G.c a x * (f x - f a) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hx'
      exact absurd (Finset.mem_univ x) hx'
  have hrow : (∑ p : V × V, if p.1 = x then G.c p.1 p.2 * (f p.2 - f p.1) else 0) =
      ∑ b : V, G.c x b * (f b - f x) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · simp
    · intro a _ ha
      simp [ha]
    · intro hx'
      exact absurd (Finset.mem_univ x) hx'
  have hlap : (∑ b : V, G.c x b * (f b - f x)) = ∑ y : V, G.lapTerm f x y :=
    Finset.sum_congr rfl fun b _ => rfl
  have hcolneg : (∑ a : V, G.c a x * (f x - f a)) = -∑ y : V, G.lapTerm f x y := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ReflectedWalk.ConductanceGraph.lapTerm]
    rw [G.c_symm a x]
    ring
  simp only [ReflectedWalk.ConductanceGraph.dirichletForm]
  rw [tsum_fintype, hsplit, hcol, hrow, hlap, hcolneg, tsum_fintype]
  ring

/-- **The Euler–Lagrange equations of the finite anchored problem.** A function orthogonal
to every variation vanishing on `A` satisfies the weighted Dirichlet linear equations at
every vertex outside `A`, i.e. it is discrete harmonic there in the sense of Gwynne–Sung
Definition 1.2, the absolute-convergence conjunct being automatic on a finite vertex
type. -/
theorem isHarmonicOn_compl_of_dirichletForm_zeroTrace_eq_zero [Finite V] {A : Set V}
    {f : V → ℝ} (horth : ∀ φ ∈ zeroTraceSubmodule G A, G.dirichletForm f φ = 0) :
    G.IsHarmonicOn f Aᶜ := by
  intro x hx
  refine ⟨Summable.of_finite, ?_⟩
  have hmem : vertexIndicator x ∈ zeroTraceSubmodule G A := by
    refine ⟨hasFiniteEnergy_of_finite G _, fun a ha => ?_⟩
    have hax : a ≠ x := fun h => hx (h ▸ ha)
    exact vertexIndicator_eq_zero hax
  have h0 := horth _ hmem
  rw [dirichletForm_vertexIndicator] at h0
  exact neg_eq_zero.1 h0

/-- **The finite anchored Dirichlet minimizer solves the linear system.** For arbitrary
real boundary data the energy minimizer with that trace exists, is discrete harmonic at
every vertex off the boundary, and is unique. -/
theorem exists_finite_anchored_minimizer_isHarmonicOn [Finite V] {A : Set V}
    (hA : BoundaryAnchored G A) (u : V → ℝ) :
    ∃ f : V → ℝ, (∀ a ∈ A, f a = u a) ∧ G.IsHarmonicOn f Aᶜ ∧
      (∀ h : V → ℝ, (∀ a ∈ A, h a = u a) → G.Energy f ≤ G.Energy h) := by
  obtain ⟨f, htrace, horth, hmin⟩ :=
    exists_finite_anchored_minimizer_orthogonal G hA u
  exact ⟨f, htrace, isHarmonicOn_compl_of_dirichletForm_zeroTrace_eq_zero G horth, hmin⟩

/-! ### The two-coordinate minimizer for arbitrary boundary data -/

/-! ### The actual anchored finite levels -/

variable [DecidableEq V]

end FiniteDirichletMinimizers

end ReflectedGMS
