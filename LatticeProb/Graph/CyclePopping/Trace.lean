module

/-
Chronological traces on arrow stacks. Consuming a trace advances the cursor at every
departure. A closed simple excursion follows one visible cycle, so its consumption is
exactly one legal cycle pop. The proofs retain the complete original quiver arrows.
-/
public import LatticeProb.Graph.CyclePopping.Basic
public import LatticeProb.Combinatorics.LoopErasure.Composition

@[expose] public section

/-!
Chronological traces on arrow stacks. Consuming a trace advances the cursor at every
departure. A closed simple excursion follows one visible cycle, so its consumption is
exactly one legal cycle pop. The proofs retain the complete original quiver arrows.
-/

set_option autoImplicit false

namespace LatticeProb.Graph.CyclePopping

open Quiver

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- A vertex stack stores the endpoint together with its actual outgoing arrow. -/
abbrev ArrowStacks := Stacks (fun v : V => Σ w : V, v ⟶ w)

/-- The departure vertices of a path, with chronological multiplicities. -/
def departures {a b : V} (p : Path a b) : List V := p.vertices.dropLast

/-- Consume every chronological departure, retaining the full visit multiplicities. -/
def consume (k : Cursor V) {a : V} : {b : V} → Path a b → Cursor V
  | _, .nil => k
  | _, @Path.cons _ _ _ b _ p _ => pop (consume k p) {b}

/-- Every arrow in the path equals the selected stack arrow at its departure vertex. -/
def selected (σ : ArrowStacks (V := V)) (k : Cursor V) {a : V} :
    {b : V} → Path a b → Prop
  | _, .nil => True
  | c, @Path.cons _ _ _ b _ p e => selected σ k p ∧ σ b (k b) = ⟨c, e⟩

/-- Every arrow of a raw trace is read at the cursor left by its previous departures. -/
def reads (σ : ArrowStacks (V := V)) (k : Cursor V) {a : V} :
    {b : V} → Path a b → Prop
  | _, .nil => True
  | c, @Path.cons _ _ _ b _ p e => reads σ k p ∧ σ b (consume k p b) = ⟨c, e⟩

/-- A path follows an outgoing function at each of its arrows. -/
def follows (f : V → V) {a : V} : {b : V} → Path a b → Prop
  | _, .nil => True
  | c, @Path.cons _ _ _ b _ p _ => follows f p ∧ f b = c

omit [DecidableEq V] in
/-- Appending an arrow adds its source to the list of departures. -/
theorem departures_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    departures (p.cons e) = departures p ++ [b] := by
  rw [departures, Path.vertices_cons, List.concat_eq_append, List.dropLast_concat]
  exact (Path.dropLast_append_end_eq p).symm

/-- Trace consumption respects concatenation, including repeated visits. -/
theorem consume_comp (k : Cursor V) {a b c : V} (p : Path a b) (q : Path b c) :
    consume k (p.comp q) = consume (consume k p) q := by
  induction q with
  | nil => rfl
  | cons q e ih => exact congrArg (fun l => pop l {_}) ih

/-- On a path without repeated vertices, consumption increments each departure once. -/
theorem consume_of_nodup (k : Cursor V) {a b : V} (p : Path a b)
    (hp : p.vertices.Nodup) : consume k p = pop k (departures p).toFinset := by
  induction p with
  | nil =>
    funext v
    simp only [consume, departures, Path.vertices_nil, List.dropLast_singleton,
      List.toFinset_nil, pop, Finset.notMem_empty, if_false]
  | @cons b c p e ih =>
    have hn := (List.nodup_concat p.vertices c).mp hp
    have hb : b ∉ departures p := by
      have hnd := (Path.dropLast_append_end_eq p) ▸ hn.2
      intro hm
      exact (List.nodup_append.mp hnd).2.2 b hm b (List.mem_singleton.mpr rfl) rfl
    rw [consume, ih hn.2, departures_cons, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    change pop (pop k (departures p).toFinset) {b} =
      pop k ((departures p).toFinset ∪ {b})
    funext v
    by_cases hv : v = b
    · subst v
      simp only [pop, Finset.mem_singleton, if_true, List.mem_toFinset, hb, if_false,
        Finset.mem_union, or_true]
    · simp only [pop, Finset.mem_singleton, hv, if_false, Finset.mem_union, or_false]

omit [DecidableEq V] in
/-- A selected path follows the endpoint function of the visible stack arrows. -/
theorem selected_follows (σ : ArrowStacks (V := V)) (k : Cursor V)
    {a b : V} (p : Path a b) (hp : selected σ k p) :
    follows (next (fun _ s => s.1) σ k) p := by
  induction p with
  | nil => trivial
  | cons p e ih =>
    exact ⟨ih hp.1, congrArg Sigma.fst hp.2⟩

omit [DecidableEq V] in
/-- Following a visible function for the length of a path reaches its endpoint. -/
theorem follows_iterate_end (f : V → V) {a b : V} (p : Path a b)
    (hp : follows f p) : f^[p.length] a = b := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [Path.length_cons, Function.iterate_succ_apply', ih hp.1]
    exact hp.2

omit [DecidableEq V] in
/-- Every visited vertex is an iterate of the visible outgoing function. -/
theorem follows_vertex_iterate (f : V → V) {a b : V} (p : Path a b)
    (hp : follows f p) {v : V} (hv : v ∈ p.vertices) :
    ∃ n ≤ p.length, f^[n] a = v := by
  induction p with
  | nil =>
    have he : v = a := List.mem_singleton.mp hv
    exact ⟨0, le_refl 0, he.symm⟩
  | cons p e ih =>
    rcases (Path.mem_vertices_cons _ _).mp hv with hv | rfl
    · obtain ⟨n, hn, he⟩ := ih hp.1 hv
      exact ⟨n, Nat.le_succ_of_le hn, he⟩
    · exact ⟨_, le_refl _, follows_iterate_end f _ hp⟩

omit [DecidableEq V] in
/-- The visible successor of any departure remains on the path. -/
theorem follows_successor_mem (f : V → V) {a b : V} (p : Path a b)
    (hp : follows f p) {v : V} (hv : v ∈ departures p) : f v ∈ p.vertices := by
  induction p with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons p e ih =>
    rw [departures_cons] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact (Path.mem_vertices_cons _ _).mpr (Or.inl (ih hp.1 hv))
    · have he := List.mem_singleton.mp hv
      subst v
      exact (Path.mem_vertices_cons _ _).mpr (Or.inr hp.2)

/-- A closed visible excursion is a genuine directed cycle on its visited vertices.
No cycle-realization hypothesis is assumed: closure and mutual reachability are derived. -/
theorem is_cycle_of_closed_follows (R : Set V) (f : V → V) {a b : V}
    (p : Path a b) (e : b ⟶ a) (hp : follows f (p.cons e))
    (hR : ∀ v ∈ p.vertices, v ∉ R) : IsCycle R f p.vertices.toFinset := by
  have hdep : departures (p.cons e) = p.vertices := by
    rw [departures_cons, departures, Path.dropLast_append_end_eq]
  refine ⟨⟨a, List.mem_toFinset.mpr (Path.start_mem_vertices p)⟩,
    fun v hv => hR v (List.mem_toFinset.mp hv), ?_, ?_⟩
  · intro v hv
    have hm := follows_successor_mem f (p.cons e) hp
      (hdep.symm ▸ List.mem_toFinset.mp hv)
    rcases (Path.mem_vertices_cons _ _).mp hm with hm | hm
    · exact List.mem_toFinset.mpr hm
    · rw [hm]
      exact List.mem_toFinset.mpr (Path.start_mem_vertices p)
  · intro v hv w hw
    obtain ⟨i, hi, hvi⟩ := follows_vertex_iterate f p hp.1 (List.mem_toFinset.mp hv)
    obtain ⟨j, _, hwj⟩ := follows_vertex_iterate f p hp.1 (List.mem_toFinset.mp hw)
    have hiN : i ≤ (p.cons e).length := Nat.le_succ_of_le hi
    have hback : f^[(p.cons e).length - i] v = a := by
      rw [← hvi, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hiN]
      exact follows_iterate_end f _ hp
    exact ⟨j + ((p.cons e).length - i), by
      rw [Function.iterate_add_apply, hback, hwj]⟩

/-- **Chronological closed excursions pop legal cycles.** A simple retained excursion
whose closing arrow returns to its start consumes exactly one visible directed cycle,
using the same arrows and the literal initial cursors. -/
theorem closed_excursion_pop (R : Set V) (σ : ArrowStacks (V := V)) (k : Cursor V)
    {a b : V} (p : Path a b) (e : b ⟶ a) (hp : p.vertices.Nodup)
    (hs : selected σ k (p.cons e)) (hR : ∀ v ∈ p.vertices, v ∉ R) :
    pop_step R (fun _ s => s.1) σ k (consume k (p.cons e)) := by
  refine ⟨p.vertices.toFinset,
    is_cycle_of_closed_follows R _ p e (selected_follows σ k _ hs) hR, ?_⟩
  rw [consume, consume_of_nodup k p hp, ← Path.dropLast_append_end_eq p,
    List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
  have hb : b ∉ departures p := by
    have hnd := (Path.dropLast_append_end_eq p) ▸ hp
    intro hm
    exact (List.nodup_append.mp hnd).2.2 b hm b (List.mem_singleton.mpr rfl) rfl
  change pop (pop k (departures p).toFinset) {b} =
    pop k ((departures p).toFinset ∪ {b})
  funext v
  by_cases hv : v = b
  · subst v
    simp only [pop, Finset.mem_singleton, if_true, List.mem_toFinset, hb, if_false,
      Finset.mem_union, or_true]
  · simp only [pop, Finset.mem_singleton, hv, if_false, Finset.mem_union, or_false]

end LatticeProb.Graph.CyclePopping
