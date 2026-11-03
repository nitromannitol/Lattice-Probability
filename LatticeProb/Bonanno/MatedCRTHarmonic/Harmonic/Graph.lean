/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Harmonic.Graph at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dsrc
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import Mathlib

/-!
# Graph facts for harmonic measure

For a locally finite multigraph `G` (`LFMultigraph`):

* adjacency comes from an edge, oriented either way (`adj_iff`), and gives a dart
  (`exists_dart_of_adj`); membership in `outDarts` is `dsrc d = x` (`mem_outDarts`);
* neighbourhoods and graph balls are finite (`finite_adj`, `finite_edist_le`); hence a connected
  `G` has countably many vertices and edges (`countable_of_connected`, `countable_edge`);
* the filter `awayFrom A` (`dist(x, A) → ∞`) is proper for finite `A` on infinite `G`
  (`awayFrom_neBot_holds`) and eventually avoids `A` (`eventually_notMem_awayFrom`);
* the edge boundary of a finite set is finite (`finite_edgeBoundary`), and a dart from outside
  `A` into `A` carries a boundary edge (`fst_mem_edgeBoundary`).
-/

set_option autoImplicit false

open Filter Set
open scoped ENNReal Topology

namespace MatedCRTHarmonic.Harmonic

variable {V E : Type*} (G : LFMultigraph V E)

theorem adj_iff {x y : V} :
    G.adj.Adj x y ↔ x ≠ y ∧
      ((∃ e, G.src e = x ∧ G.tgt e = y) ∨ (∃ e, G.src e = y ∧ G.tgt e = x)) := by
  rw [LFMultigraph.adj, SimpleGraph.fromRel_adj]

theorem dsrc_false (e : E) : G.dsrc (e, false) = G.src e := rfl
theorem dsrc_true (e : E) : G.dsrc (e, true) = G.tgt e := rfl
theorem dtgt_false (e : E) : G.dtgt (e, false) = G.tgt e := rfl
theorem dtgt_true (e : E) : G.dtgt (e, true) = G.src e := rfl

/-- The darts leaving `x` are exactly those with source `x`. -/
theorem mem_outDarts {x : V} {d : G.Dart} : d ∈ G.outDarts x ↔ G.dsrc d = x := by
  classical
  obtain ⟨e, b⟩ := d
  unfold LFMultigraph.outDarts
  simp only [Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ,
    and_true, Set.mem_ofPred_eq, and_iff_right_iff_imp]
  cases b
  · intro h; exact Or.inl h
  · intro h; exact Or.inr h

/-- An adjacency is traversed by a dart. -/
theorem exists_dart_of_adj {x y : V} (h : G.adj.Adj x y) :
    ∃ d : G.Dart, G.dsrc d = x ∧ G.dtgt d = y := by
  obtain ⟨-, ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩⟩ := (adj_iff G).mp h
  · exact ⟨(e, false), he1, he2⟩
  · exact ⟨(e, true), he2, he1⟩

/-- The two ends of an edge are adjacent when distinct. -/
theorem adj_of_edge {e : E} (h : G.src e ≠ G.tgt e) : G.adj.Adj (G.src e) (G.tgt e) :=
  (adj_iff G).mpr ⟨h, Or.inl ⟨e, rfl, rfl⟩⟩

theorem finite_adj (y : V) : {x | G.adj.Adj x y}.Finite := by
  refine (((G.finite_inc y).image G.src).union ((G.finite_inc y).image G.tgt)).subset ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  obtain ⟨-, ⟨e, he1, he2⟩ | ⟨e, he1, he2⟩⟩ := (adj_iff G).mp hx
  · exact Or.inl ⟨e, Or.inr he2, he1⟩
  · exact Or.inr ⟨e, Or.inl he1, he2⟩

/-- Graph balls are finite. -/
theorem finite_edist_le (a : V) (n : ℕ) : {x | G.adj.edist x a ≤ n}.Finite := by
  induction n with
  | zero =>
    refine (Set.finite_singleton a).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq, Nat.cast_zero, nonpos_iff_eq_zero,
      SimpleGraph.edist_eq_zero_iff] at hx
    exact hx
  | succ n ih =>
    refine (ih.union (ih.biUnion fun y _ => finite_adj G y)).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx
    have hne : G.adj.edist x a ≠ ⊤ := ne_top_of_le_ne_top (by simp) hx
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
    cases p with
    | nil => exact Or.inl (by simp)
    | @cons _ y _ h q =>
      refine Or.inr (Set.mem_biUnion (x := y) ?_ h)
      simp only [Set.mem_ofPred_eq]
      rw [SimpleGraph.Walk.length_cons] at hp
      calc G.adj.edist y a ≤ q.length := SimpleGraph.edist_le q
        _ ≤ n := by
          have h1 : ((q.length + 1 : ℕ) : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by
            rw [hp]; exact_mod_cast hx
          have h2 : q.length + 1 ≤ n + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : q.length ≤ n)

/-- A connected locally finite multigraph has countably many vertices. -/
theorem countable_of_connected (hconn : G.adj.Connected) : Countable V := by
  obtain ⟨a⟩ := hconn.nonempty
  have hU : (⋃ n : ℕ, {x | G.adj.edist x a ≤ n}) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ?_
    have hne : G.adj.edist x a ≠ ⊤ :=
      SimpleGraph.edist_ne_top_iff_reachable.mpr (hconn.preconnected x a)
    exact ⟨(G.adj.edist x a).toNat, by simp [ENat.natCast_toNat hne]⟩
  have hc : (Set.univ : Set V).Countable :=
    hU ▸ Set.countable_iUnion fun n => (finite_edist_le G a n).countable
  exact Set.countable_univ_iff.mp hc

include G in
/-- Countably many vertices give countably many edges. -/
theorem countable_edge [Countable V] : Countable E := by
  have hU : (⋃ x : V, {e : E | G.src e = x ∨ G.tgt e = x}) = Set.univ :=
    Set.eq_univ_of_forall fun e => Set.mem_iUnion.mpr ⟨G.src e, Or.inl rfl⟩
  have hc : (Set.univ : Set E).Countable :=
    hU ▸ Set.countable_iUnion fun x => (G.finite_inc x).countable
  exact Set.countable_univ_iff.mp hc

end MatedCRTHarmonic.Harmonic
