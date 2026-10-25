module

/-
Chronological loop erasure produces a finite legal cycle-pop run. The induction keeps
two distinct cursors: the cursor after all raw departures and the cursor after deleted
cycles. Retained arrows remain selected at the latter cursor, and consuming that retained
path accounts exactly for the difference. At each revisit the retained suffix is one
simple visible cycle, whose legality is derived from its actual arrows.
-/
public import LatticeProb.Graph.CyclePopping.Trace

@[expose] public section

/-!
Chronological loop erasure produces a finite legal cycle-pop run. The induction keeps
two distinct cursors: the cursor after all raw departures and the cursor after deleted
cycles. Retained arrows remain selected at the latter cursor, and consuming that retained
path accounts exactly for the difference. At each revisit the retained suffix is one
simple visible cycle, whose legality is derived from its actual arrows.
-/

set_option autoImplicit false

namespace LatticeProb.Graph.CyclePopping

open Quiver LatticeProb.Combinatorics.LoopErasure

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- Consumption commutes with a fixed finite cursor increment. -/
theorem consume_pop (k : Cursor V) (c : Finset V) {a b : V} (p : Path a b) :
    consume (pop k c) p = pop (consume k p) c := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [consume, ih, consume]
    exact pop_comm _ c {_}

/-- A simple path never consumes its terminal vertex. -/
theorem consume_end (k : Cursor V) {a b : V} (p : Path a b)
    (hp : p.vertices.Nodup) : consume k p b = k b := by
  rw [consume_of_nodup k p hp]
  apply pop_apply_of_not_mem
  intro hm
  have hnd := (Path.dropLast_append_end_eq p) ▸ hp
  exact (List.nodup_append.mp hnd).2.2 b (List.mem_toFinset.mp hm)
    b (List.mem_singleton.mpr rfl) rfl

omit [DecidableEq V] in
/-- Selection of a concatenation is selection of both pieces at the same cursor. -/
theorem selected_comp (σ : ArrowStacks (V := V)) (k : Cursor V)
    {a b c : V} (p : Path a b) (q : Path b c) :
    selected σ k (p.comp q) ↔ selected σ k p ∧ selected σ k q := by
  induction q with
  | nil => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | cons q e ih =>
    change (selected σ k (p.comp q) ∧ _) ↔ _
    rw [ih]
    exact and_assoc

omit [DecidableEq V] in
/-- Selection depends only on the stack cells at actual departure vertices. -/
theorem selected_congr (σ : ArrowStacks (V := V)) {k l : Cursor V}
    {a b : V} (p : Path a b) (hp : selected σ k p)
    (he : ∀ v ∈ departures p, k v = l v) : selected σ l p := by
  induction p with
  | nil => trivial
  | @cons b c p e ih =>
    refine ⟨ih hp.1 (fun v hv => he v (by
      rw [departures_cons]
      exact List.mem_append_left _ hv)), ?_⟩
    rw [← he b (by rw [departures_cons]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl))]
    exact hp.2

/-- Consumption of a simple path followed by an arrow to its start is one set increment. -/
theorem consume_closed (k : Cursor V) {a b : V} (p : Path a b) (e : b ⟶ a)
    (hp : p.vertices.Nodup) : consume k (p.cons e) = pop k p.vertices.toFinset := by
  have hb : b ∉ departures p := by
    intro hm
    have hnd := (Path.dropLast_append_end_eq p) ▸ hp
    exact (List.nodup_append.mp hnd).2.2 b hm b (List.mem_singleton.mpr rfl) rfl
  rw [consume, consume_of_nodup k p hp, ← Path.dropLast_append_end_eq p,
    List.toFinset_append]
  change pop (pop k (departures p).toFinset) {b} = pop k ((departures p).toFinset ∪ {b})
  funext v
  by_cases hv : v = b
  · subst v
    simp only [pop, Finset.mem_singleton, if_true, List.mem_toFinset, hb, if_false,
      Finset.mem_union, or_true]
  · simp only [pop, Finset.mem_singleton, hv, if_false, Finset.mem_union, or_false]

/-- **Loop erasure realizes legal cycle popping.** Every finite raw trace read from
literal arrow stacks, avoiding roots at its departures, produces a finite legal pop run.
Its retained arrows are exactly selected top arrows. The consumed raw cursor equals
the cursor obtained by subsequently consuming the retained path; no visit is discarded
from this accounting identity. -/
theorem loop_erase_pop_run (R : Set V) (σ : ArrowStacks (V := V)) (k : Cursor V)
    {a b : V} (p : Path a b) (hp : reads σ k p)
    (hR : ∀ v ∈ departures p, v ∉ R) :
    ∃ l : Cursor V, Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k l ∧
      selected σ l (loopErase p) ∧ consume l (loopErase p) = consume k p := by
  induction p with
  | nil => exact ⟨k, .refl, trivial, rfl⟩
  | @cons b c p e ih =>
    have hRold : ∀ v ∈ departures p, v ∉ R := fun v hv => hR v (by
      rw [departures_cons]
      exact List.mem_append_left _ hv)
    obtain ⟨l, hl, hs, hconsume⟩ := ih hp.1 hRold
    have hn := loopErase_vertices_nodup p
    have he : σ b (l b) = ⟨c, e⟩ := by
      have hc := congrFun hconsume b
      rw [consume_end l (loopErase p) hn] at hc
      rw [hc]
      exact hp.2
    have hqR : ∀ v ∈ (loopErase p).vertices, v ∉ R := by
      intro v hv
      apply hR v
      rw [departures_cons, departures, Path.dropLast_append_end_eq]
      exact (loopErase_vertices_sublist p).subset hv
    by_cases hc : c ∈ (loopErase p).vertices
    · obtain ⟨u, q, huq⟩ := (loopErase p).exists_eq_comp_of_mem_vertices hc
      have hsplit : (u.vertices.dropLast ++ q.vertices).Nodup := by
        rw [← Path.vertices_comp, ← huq]
        exact hn
      have hqn : q.vertices.Nodup := (List.nodup_append.mp hsplit).2.1
      have hsel := (selected_comp σ l u q).mp (huq ▸ hs)
      have hcycle : pop_step R (fun _ s => s.1) σ l (pop l q.vertices.toFinset) := by
        have hpcycle := closed_excursion_pop R σ l q e hqn ⟨hsel.2, he⟩
          (fun v hv => hqR v (huq.symm ▸ (mem_vertices_comp u q v).mpr (Or.inr hv)))
        rw [consume_closed l q e hqn] at hpcycle
        exact hpcycle
      have hprefix : selected σ (pop l q.vertices.toFinset) u := by
        apply selected_congr σ u hsel.1
        intro v hv
        symm
        apply pop_apply_of_not_mem
        intro hmem
        exact (List.nodup_append.mp hsplit).2.2 v hv v (List.mem_toFinset.mp hmem) rfl
      have hpre : prefixTo (loopErase p) c hc = u := by
        simpa only [← huq] using prefixTo_comp_start u q hqn (huq ▸ hc)
      refine ⟨pop l q.vertices.toFinset, hl.tail hcycle, ?_, ?_⟩
      · rw [loopErase, dif_pos hc, hpre]
        exact hprefix
      · rw [loopErase, dif_pos hc, hpre, consume_pop, consume,
          ← hconsume, huq]
        change pop (consume l u) q.vertices.toFinset = consume l (u.comp (q.cons e))
        rw [consume_comp, consume_closed (consume l u) q e hqn]
    · refine ⟨l, hl, ?_, ?_⟩
      · rw [loopErase, dif_neg hc]
        exact ⟨hs, he⟩
      · rw [loopErase, dif_neg hc, consume, consume, hconsume]

/-- Chronological consumption adds the exact number of departures from each vertex. -/
theorem consume_apply (k : Cursor V) {a b : V} (p : Path a b) (v : V) :
    consume k p v = k v + (departures p).count v := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
    rw [consume, departures_cons, List.count_append]
    by_cases hv : v = b
    · subst v
      rw [pop_apply_of_mem _ _ (Finset.mem_singleton_self _), ih]
      simp only [List.count_cons_self, List.count_nil, Nat.add_assoc]
    · rw [pop_apply_of_not_mem _ _ (fun h => hv (Finset.mem_singleton.mp h)), ih]
      rw [List.count_cons_of_ne (Ne.symm hv), List.count_nil, Nat.add_zero]

/-- The literal cursor after deleting chronological cycles: subtract precisely the
retained departures from the full consumed cursor. In `loop_erase_cursor_spec` the
subtraction is proved exact, so it introduces no off-trace fallback semantics. -/
def erasedCursor (k : Cursor V) {a b : V} (p : Path a b) : Cursor V :=
  fun v => consume k p v - (departures (loopErase p)).count v

/-- **Exact chronological pop cursor.** The cursor computed from the full raw trace
is reached by legal cycle pops, selects every original retained arrow, and has the exact
raw-versus-retained departure accounting identity. -/
theorem loop_erase_cursor_spec (R : Set V) (σ : ArrowStacks (V := V)) (k : Cursor V)
    {a b : V} (p : Path a b) (hp : reads σ k p)
    (hR : ∀ v ∈ departures p, v ∉ R) :
    Relation.ReflTransGen (pop_step R (fun _ s => s.1) σ) k (erasedCursor k p) ∧
      selected σ (erasedCursor k p) (loopErase p) ∧
      consume (erasedCursor k p) (loopErase p) = consume k p := by
  obtain ⟨l, hl, hs, hc⟩ := loop_erase_pop_run R σ k p hp hR
  have he : erasedCursor k p = l := by
    funext v
    unfold erasedCursor
    rw [← congrFun hc v, consume_apply]
    exact Nat.add_sub_cancel _ _
  rw [he]
  exact ⟨hl, hs, hc⟩

end LatticeProb.Graph.CyclePopping
