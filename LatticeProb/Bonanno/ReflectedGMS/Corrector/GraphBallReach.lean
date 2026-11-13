/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GraphBallReach at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# A measurable, similarity-invariant reachability weight on code slots

The re-rooting statement behind `hnbr` transports the specific-energy density from a whole
graph ball back to the root cell.  The transport kernel therefore has to carry the
combinatorial indicator `1_{d_G(u,v) ≤ k}`, and a `MassTransportKernel` needs that indicator

* **measurable** as a function of the environment, and
* **invariant** under the relabelling induced by a physical similarity.

`SimpleGraph.edist` on the subtype `Code.Vertex e.val` is neither of those things directly:
it is defined through an existential over walks in a graph whose *vertex type itself* depends
on `e`.  This module replaces it by a slot-level recursion on the raw conductance matrix
`e.val.2 : ℕ → ℕ → ℝ`, which has a fixed index type and is manifestly measurable.

* `reach c k n n'` — one step of neighbour saturation, `k` times: it is `1` when `n'` can be
  reached from `n` along at most `k` edges of positive conductance, `0` otherwise
  (`reach_le_one`, `one_le_reach_self`).
* `one_le_reach_of_mem_ball` — the only comparison the transport needs: every vertex of the
  graph ball `B(r, k+1)` is reached, so `reach` dominates the indicator of the ball.
* `reach_eq_zero_of_absent_source` — absent slots carry no conductance
  (`Code.AdmissibleConductance.absent`) and therefore reach nothing but themselves.  This is
  what lets a slot-indexed transport sum be rewritten as a sum over actual vertices.
* `reach_relabel` — invariance under `EnvironmentLaws.IsSimilarityRelabel`: conductances are
  similarity invariant, so reachability is a physical, not a labelling, notion.
* `measurable_reach` — measurability in the environment, by induction on the number of steps.

Nothing here is probabilistic and nothing here mentions cells, areas or densities.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GraphBallReach

open Code EnvironmentLaws

/-! ### The slot-level reachability weight -/

/-- `reach c k n n'` is `1` when the slot `n'` is reachable from the slot `n` along at most
`k` edges of positive conductance, and `0` otherwise.  The recursion is the usual neighbour
saturation: either `n'` is already reachable in `k` steps, or one first moves across an edge
out of `n`. -/
noncomputable def reach : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ≥0∞
  | _, 0, n, n' => if n = n' then 1 else 0
  | c, (k + 1), n, n' =>
      max (reach c k n n') (⨆ x : ℕ, if 0 < c n x then reach c k x n' else 0)

theorem reach_zero (c : ℕ → ℕ → ℝ) (n n' : ℕ) :
    reach c 0 n n' = if n = n' then 1 else 0 := rfl

theorem reach_succ (c : ℕ → ℕ → ℝ) (k n n' : ℕ) :
    reach c (k + 1) n n'
      = max (reach c k n n') (⨆ x : ℕ, if 0 < c n x then reach c k x n' else 0) := rfl

/-- The weight really is an indicator: it never exceeds `1`. -/
theorem reach_le_one (c : ℕ → ℕ → ℝ) (k : ℕ) : ∀ n n' : ℕ, reach c k n n' ≤ 1 := by
  induction k with
  | zero =>
      intro n n'
      rw [reach_zero]
      split
      · exact le_rfl
      · exact zero_le_one
  | succ k ih =>
      intro n n'
      rw [reach_succ]
      refine max_le (ih n n') (iSup_le fun x => ?_)
      split
      · exact ih x n'
      · exact zero_le_one

/-- Every slot reaches itself in any number of steps. -/
theorem one_le_reach_self (c : ℕ → ℕ → ℝ) (k n : ℕ) : 1 ≤ reach c k n n := by
  induction k with
  | zero => rw [reach_zero, if_pos rfl]
  | succ k ih => rw [reach_succ]; exact le_max_of_le_left ih

/-- A slot with no positive conductance at all reaches nothing but itself. -/
theorem reach_eq_zero_of_row_zero (c : ℕ → ℕ → ℝ) {n : ℕ} (hc : ∀ x, c n x = 0) (k : ℕ)
    {n' : ℕ} (hne : n ≠ n') : reach c k n n' = 0 := by
  induction k with
  | zero => rw [reach_zero, if_neg hne]
  | succ k ih =>
      have hsup : (⨆ x : ℕ, if 0 < c n x then reach c k x n' else 0) = 0 := by
        refine le_antisymm (iSup_le fun x => ?_) zero_le
        have hx : ¬ (0 < c n x) := by rw [hc x]; exact lt_irrefl 0
        rw [if_neg hx]
      rw [reach_succ, ih, hsup, max_self]

/-- The environment form: an absent slot reaches nothing but itself. -/
theorem reach_eq_zero_of_absent (e : Env) {n : ℕ} (hn : e.val.1 n = none) (k : ℕ) {n' : ℕ}
    (hne : n ≠ n') : reach e.val.2 k n n' = 0 := by
  have hadm : AdmissibleConductance e.val := e.property.choose
  exact reach_eq_zero_of_row_zero e.val.2 (fun x => hadm.absent n x (Or.inl hn)) k hne

/-! ### Reachability dominates the indicator of a graph ball -/

/-- A walk of length at most `k` is witnessed by the reachability weight. -/
theorem one_le_reach_of_walk (e : Env) {v v' : Vertex e.val}
    (p : (decode e).graph.toSimpleGraph.Walk v v') :
    ∀ k : ℕ, p.length ≤ k → 1 ≤ reach e.val.2 k v.val v'.val := by
  induction p with
  | nil => intro k _; exact one_le_reach_self _ _ _
  | @cons a b d hadj q ih =>
      intro k hk
      cases k with
      | zero => simp only [SimpleGraph.Walk.length_cons] at hk; omega
      | succ k =>
          have hq : q.length ≤ k := by
            simp only [SimpleGraph.Walk.length_cons] at hk
            omega
          have hb : 1 ≤ reach e.val.2 k b.val d.val := ih k hq
          have hpos : 0 < e.val.2 a.val b.val := hadj
          rw [reach_succ]
          refine le_trans ?_ (le_max_right (reach e.val.2 k a.val d.val)
            (⨆ x : ℕ, if 0 < e.val.2 a.val x then reach e.val.2 k x d.val else 0))
          calc (1 : ℝ≥0∞)
              ≤ reach e.val.2 k b.val d.val := hb
            _ = (if 0 < e.val.2 a.val b.val then reach e.val.2 k b.val d.val else 0) :=
                (if_pos hpos).symm
            _ ≤ ⨆ x : ℕ, if 0 < e.val.2 a.val x then reach e.val.2 k x d.val else 0 :=
                le_iSup (fun x : ℕ =>
                  if 0 < e.val.2 a.val x then reach e.val.2 k x d.val else 0) b.val

/-- **The comparison the transport needs.**  Every vertex of the graph ball `B(r, k+1)` — the
exact ball appearing in `HarmonicMainStatement.graphNeighborhoodError` — has reachability
weight at least `1` from the centre in `k` steps. -/
theorem one_le_reach_of_mem_ball (e : Env) (r : Vertex e.val) (k : ℕ) {v : Vertex e.val}
    (hv : v ∈ (decode e).graph.toSimpleGraph.ball r ((k + 1 : ℕ) : ℕ∞)) :
    1 ≤ reach e.val.2 k r.val v.val := by
  have hcast : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := Nat.cast_add_one k
  have hvk : (decode e).graph.toSimpleGraph.edist r v ≤ (k : ℕ∞) := by
    have h1 : (decode e).graph.toSimpleGraph.edist v r < (k : ℕ∞) + 1 := by
      rw [← hcast]
      exact SimpleGraph.mem_ball.mp hv
    have h2 : (decode e).graph.toSimpleGraph.edist v r ≤ (k : ℕ∞) :=
      ENat.lt_natCast_add_one_iff.mp h1
    rwa [SimpleGraph.edist_comm] at h2
  have hne : (decode e).graph.toSimpleGraph.edist r v ≠ ⊤ := by
    intro htop
    rw [htop] at hvk
    exact (ENat.natCast_ne_top k) (top_le_iff.mp hvk)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hpk : p.length ≤ k := by
    have hle : ((p.length : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by rw [hp]; exact hvk
    exact_mod_cast hle
  exact one_le_reach_of_walk e p k hpk

/-! ### Invariance under a physical similarity -/

/-- A supremum over all slots of a weight that vanishes on absent slots is a supremum over
the actual vertices. -/
theorem iSup_slot_eq_iSup_vertex (e : Env) (g : ℕ → ℝ≥0∞)
    (hg : ∀ x : ℕ, e.val.1 x = none → g x = 0) :
    (⨆ x : ℕ, g x) = ⨆ y : Vertex e.val, g y.val := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun y => le_iSup g y.val)
  by_cases hx : (e.val.1 x).isSome = true
  · exact le_iSup (fun y : Vertex e.val => g y.val) (⟨x, hx⟩ : Vertex e.val)
  · have hnone : e.val.1 x = none := by
      cases hxx : e.val.1 x with
      | none => rfl
      | some a => rw [hxx] at hx; exact absurd rfl hx
    rw [hg x hnone]
    exact zero_le

/-- Reindexing a vertex supremum along a relabelling. -/
theorem iSup_vertex_relabel {e e' : Env} (rel : Vertex e.val ≃ Vertex e'.val)
    (f : Vertex e'.val → ℝ≥0∞) :
    (⨆ y : Vertex e'.val, f y) = ⨆ w : Vertex e.val, f (rel w) := by
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun w => le_iSup f (rel w))
  have h := le_iSup (fun w : Vertex e.val => f (rel w)) (rel.symm y)
  rwa [Equiv.apply_symm_apply] at h

/-- **Reachability is a physical notion.**  A similarity relabelling preserves conductances,
hence preserves the reachability weight. -/
theorem reach_relabel {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {rel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' rel) (k : ℕ) :
    ∀ v v' : Vertex e.val,
      reach e'.val.2 k (rel v).val (rel v').val = reach e.val.2 k v.val v'.val := by
  induction k with
  | zero =>
      intro v v'
      rw [reach_zero, reach_zero]
      by_cases hvv : v = v'
      · rw [hvv, if_pos rfl, if_pos rfl]
      · have h1 : ¬ ((rel v).val = (rel v').val) := by
          intro hval
          exact hvv (rel.injective (Subtype.ext hval))
        have h2 : ¬ (v.val = v'.val) := fun hval => hvv (Subtype.ext hval)
        rw [if_neg h1, if_neg h2]
  | succ k ih =>
      intro v v'
      have hadm' : AdmissibleConductance e'.val := e'.property.choose
      have hadm : AdmissibleConductance e.val := e.property.choose
      have hc : ∀ w : Vertex e.val,
          e'.val.2 (rel v).val (rel w).val = e.val.2 v.val w.val := fun w => h.2 v w
      have hsup' : (⨆ x : ℕ, if 0 < e'.val.2 (rel v).val x
            then reach e'.val.2 k x (rel v').val else 0)
          = ⨆ y : Vertex e'.val, if 0 < e'.val.2 (rel v).val y.val
            then reach e'.val.2 k y.val (rel v').val else 0 := by
        refine iSup_slot_eq_iSup_vertex e' _ fun x hx => ?_
        have hzero : e'.val.2 (rel v).val x = 0 := hadm'.absent (rel v).val x (Or.inr hx)
        rw [if_neg (by rw [hzero]; exact lt_irrefl 0)]
      have hsup : (⨆ x : ℕ, if 0 < e.val.2 v.val x then reach e.val.2 k x v'.val else 0)
          = ⨆ w : Vertex e.val, if 0 < e.val.2 v.val w.val
            then reach e.val.2 k w.val v'.val else 0 := by
        refine iSup_slot_eq_iSup_vertex e _ fun x hx => ?_
        have hzero : e.val.2 v.val x = 0 := hadm.absent v.val x (Or.inr hx)
        rw [if_neg (by rw [hzero]; exact lt_irrefl 0)]
      have hreindex : (⨆ y : Vertex e'.val, if 0 < e'.val.2 (rel v).val y.val
            then reach e'.val.2 k y.val (rel v').val else 0)
          = ⨆ w : Vertex e.val, if 0 < e.val.2 v.val w.val
            then reach e.val.2 k w.val v'.val else 0 := by
        rw [iSup_vertex_relabel rel (fun y : Vertex e'.val =>
          if 0 < e'.val.2 (rel v).val y.val
            then reach e'.val.2 k y.val (rel v').val else 0)]
        refine iSup_congr fun w => ?_
        rw [hc w, ih w v']
      rw [reach_succ, reach_succ, ih v v', hsup', hreindex, hsup]

/-! ### Measurability in the environment -/

/-- The raw conductance at a fixed pair of slots is measurable in the environment. -/
theorem measurable_rawConductance (n m : ℕ) :
    Measurable fun e : Env => e.val.2 n m :=
  (measurable_pi_apply m).comp
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_inclusion))

/-- **The reachability weight is measurable.**  It is built from the raw conductance matrix by
countably many suprema and maxima. -/
theorem measurable_reach (k : ℕ) :
    ∀ n n' : ℕ, Measurable fun e : Env => reach e.val.2 k n n' := by
  induction k with
  | zero =>
      intro n n'
      simp only [reach_zero]
      exact measurable_const
  | succ k ih =>
      intro n n'
      simp only [reach_succ]
      refine Measurable.max (ih n n') (Measurable.iSup fun x => ?_)
      refine Measurable.ite ?_ (ih x n') measurable_const
      exact measurableSet_lt measurable_const (measurable_rawConductance n x)

end ReflectedGMS.GraphBallReach
