/-
Finite cycle popping for vertex instruction stacks. Each vertex has its own literal
natural-number cursor and its own instruction type. Popping advances exactly the vertices
of one directed cycle. Distinct legal cycles are disjoint, their pops commute, and finite
legal runs from the same configuration have a common continuation.
-/
import Mathlib.Data.Finset.Disjoint
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

/-!
Finite cycle popping for vertex instruction stacks. Each vertex has its own literal
natural-number cursor and its own instruction type. Popping advances exactly the vertices
of one directed cycle. Distinct legal cycles are disjoint, their pops commute, and finite
legal runs from the same configuration have a common continuation.
-/

set_option autoImplicit false

namespace LatticeProb.Graph.CyclePopping

variable {V : Type*}

/-- A nonempty finite directed cycle of `f`, disjoint from the roots `R`. Closure and
mutual reachability describe a single cycle, including a one-vertex self-loop. -/
structure IsCycle (R : Set V) (f : V → V) (c : Finset V) : Prop where
  nonempty : c.Nonempty
  avoids_roots : ∀ v ∈ c, v ∉ R
  maps_to : ∀ v ∈ c, f v ∈ c
  reachable : ∀ v ∈ c, ∀ w ∈ c, ∃ n : ℕ, f^[n] v = w

/-- Every iterate of the selected outgoing map stays in a legal cycle. -/
theorem IsCycle.iterate_mem {R : Set V} {f : V → V} {c : Finset V}
    (hc : IsCycle R f c) {v : V} (hv : v ∈ c) (n : ℕ) : f^[n] v ∈ c := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hc.maps_to _ ih

/-- Two legal cycles in one functional graph are equal or disjoint. -/
theorem IsCycle.eq_or_disjoint {R : Set V} {f : V → V} {c d : Finset V}
    (hc : IsCycle R f c) (hd : IsCycle R f d) : c = d ∨ Disjoint c d := by
  by_cases h : Disjoint c d
  · exact Or.inr h
  · obtain ⟨v, hvC, hvD⟩ := Finset.not_disjoint_iff.mp h
    left
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨n, hn⟩ := hc.reachable v hvC w hw
      rw [← hn]
      exact hd.iterate_mem hvD n
    · intro w hw
      obtain ⟨n, hn⟩ := hd.reachable v hvD w hw
      rw [← hn]
      exact hc.iterate_mem hvC n

private theorem iterate_eq_on {f g : V → V} {c : Finset V}
    (hclosed : ∀ v ∈ c, f v ∈ c) (heq : ∀ v ∈ c, f v = g v)
    {v : V} (hv : v ∈ c) (n : ℕ) : f^[n] v = g^[n] v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← heq v hv]
    exact ih (hclosed v hv)

/-- A cycle stays legal when its actual selected outgoing values stay unchanged on it. -/
theorem IsCycle.congr {R : Set V} {f g : V → V} {c : Finset V}
    (hc : IsCycle R f c) (heq : ∀ v ∈ c, f v = g v) : IsCycle R g c := by
  refine ⟨hc.nonempty, hc.avoids_roots, ?_, ?_⟩
  · intro v hv
    rw [← heq v hv]
    exact hc.maps_to v hv
  · intro v hv w hw
    obtain ⟨n, hn⟩ := hc.reachable v hv w hw
    exact ⟨n, (iterate_eq_on hc.maps_to heq hv n).symm.trans hn⟩

/-- The stack at `v` lists actual instructions of the vertex-dependent type `A v`. -/
abbrev Stacks (A : V → Type*) := (v : V) → ℕ → A v

/-- A stack cursor records how many instructions have been popped at each vertex. -/
abbrev Cursor (V : Type*) := V → ℕ

variable {A : V → Type*}

/-- The currently selected instruction at each vertex is its stack entry at its cursor. -/
def top (σ : Stacks A) (k : Cursor V) : (v : V) → A v :=
  fun v => σ v (k v)

/-- The selected outgoing endpoint is read from the actual top instruction. -/
def next (head : (v : V) → A v → V) (σ : Stacks A) (k : Cursor V) : V → V :=
  fun v => head v (top σ k v)

variable [DecidableEq V]

/-- Popping a finite set advances each of its cursors by one and leaves all others fixed. -/
def pop (k : Cursor V) (c : Finset V) : Cursor V :=
  fun v => if v ∈ c then k v + 1 else k v

/-- A cursor advances by exactly one at a popped vertex. -/
theorem pop_apply_of_mem (k : Cursor V) (c : Finset V) {v : V} (hv : v ∈ c) :
    pop k c v = k v + 1 := if_pos hv

/-- A cursor is unchanged outside the popped set. -/
theorem pop_apply_of_not_mem (k : Cursor V) (c : Finset V) {v : V} (hv : v ∉ c) :
    pop k c v = k v := if_neg hv

/-- The actual selected instruction is unchanged outside the popped set. -/
theorem top_pop_of_not_mem (σ : Stacks A) (k : Cursor V) (c : Finset V)
    {v : V} (hv : v ∉ c) : top σ (pop k c) v = top σ k v := by
  unfold top
  rw [pop_apply_of_not_mem k c hv]

/-- Finite cursor increments commute, even if the two sets overlap. -/
theorem pop_comm (k : Cursor V) (c d : Finset V) : pop (pop k c) d = pop (pop k d) c := by
  funext v
  by_cases hc : v ∈ c <;> by_cases hd : v ∈ d <;>
    simp only [pop, hc, hd, if_true, if_false]

/-- Popping can only increase vertex cursors. -/
theorem le_pop (k : Cursor V) (c : Finset V) : k ≤ pop k c := by
  intro v
  by_cases hv : v ∈ c
  · rw [pop_apply_of_mem k c hv]
    exact Nat.le_succ (k v)
  · rw [pop_apply_of_not_mem k c hv]

/-- Popping a disjoint set preserves legality of a cycle and its selected instructions. -/
theorem IsCycle.pop_disjoint (head : (v : V) → A v → V) (σ : Stacks A)
    {R : Set V} {k : Cursor V} {c d : Finset V}
    (hc : IsCycle R (next head σ k) c) (hcd : Disjoint c d) :
    IsCycle R (next head σ (pop k d)) c := by
  apply hc.congr
  intro v hv
  unfold next
  rw [top_pop_of_not_mem σ k d (Finset.disjoint_left.mp hcd hv)]

/-- One legal cycle pop, using the outgoing map selected by the literal cursors. -/
def pop_step (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    (k l : Cursor V) : Prop :=
  ∃ c : Finset V, IsCycle R (next head σ k) c ∧ l = pop k c

/-- Every finite legal pop run increases cursors coordinatewise. -/
theorem pop_run_le (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l : Cursor V} (h : Relation.ReflTransGen (pop_step R head σ) k l) : k ≤ l := by
  induction h with
  | refl => exact le_refl k
  | tail _ hstep ih =>
    obtain ⟨c, _, rfl⟩ := hstep
    exact le_trans ih (le_pop _ c)

/-- Finite legal popping never advances a root's cursor. -/
theorem pop_run_root_cursor (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l : Cursor V} (h : Relation.ReflTransGen (pop_step R head σ) k l)
    {v : V} (hv : v ∈ R) : l v = k v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨c, hc, rfl⟩ := hstep
    rw [pop_apply_of_not_mem _ c (fun hvc => hc.avoids_roots v hvc hv)]
    exact ih

/-- A finite legal run ending at `l` uses only instructions strictly below the final
cursors. Changing all other stack cells preserves that same finite run. -/
theorem pop_run_congr_below (R : Set V) (head : (v : V) → A v → V)
    {σ τ : Stacks A} {k l : Cursor V}
    (h : Relation.ReflTransGen (pop_step R head σ) k l)
    (hagrees : ∀ v i, i < l v → σ v i = τ v i) :
    Relation.ReflTransGen (pop_step R head τ) k l := by
  revert hagrees
  induction h with
  | refl => intro _; exact .refl
  | @tail m l hkm hml ih =>
    obtain ⟨c, hc, rfl⟩ := hml
    intro hagrees
    have hprefix := ih (fun v i hi => hagrees v i (lt_of_lt_of_le hi (le_pop m c v)))
    apply hprefix.tail
    refine ⟨c, hc.congr ?_, rfl⟩
    intro v hv
    unfold next top
    apply congrArg (head v)
    apply hagrees
    rw [pop_apply_of_mem m c hv]
    exact Nat.lt_succ_self (m v)

/-- Reachability of a fixed final cursor depends only on the stack cells strictly below
it; terminal top cells are absent from this condition. -/
theorem pop_run_iff_of_agree_below (R : Set V) (head : (v : V) → A v → V)
    {σ τ : Stacks A} {k l : Cursor V}
    (hagrees : ∀ v i, i < l v → σ v i = τ v i) :
    Relation.ReflTransGen (pop_step R head σ) k l ↔
      Relation.ReflTransGen (pop_step R head τ) k l :=
  ⟨fun h => pop_run_congr_below R head h hagrees,
    fun h => pop_run_congr_below R head h (fun v i hi => (hagrees v i hi).symm)⟩

/-- Two legal one-step pops are equal or admit the same legal second-pop result. -/
theorem pop_step_diamond (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l m : Cursor V} (hl : pop_step R head σ k l)
    (hm : pop_step R head σ k m) :
    ∃ n, Relation.ReflGen (pop_step R head σ) l n ∧
      Relation.ReflTransGen (pop_step R head σ) m n := by
  obtain ⟨c, hc, rfl⟩ := hl
  obtain ⟨d, hd, rfl⟩ := hm
  rcases hc.eq_or_disjoint hd with h | h
  · subst d
    exact ⟨pop k c, .refl, .refl⟩
  · refine ⟨pop (pop k c) d, .single ⟨d, hd.pop_disjoint head σ h.symm, rfl⟩,
      .single ⟨c, hc.pop_disjoint head σ h, ?_⟩⟩
    exact pop_comm k c d

/-- **Finite abelian cycle popping.** Two finite legal runs from the same cursors have a
common finite legal continuation. No termination or order-independence premise is used. -/
theorem pop_step_confluent (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l m : Cursor V} (hl : Relation.ReflTransGen (pop_step R head σ) k l)
    (hm : Relation.ReflTransGen (pop_step R head σ) k m) :
    ∃ n, Relation.ReflTransGen (pop_step R head σ) l n ∧
      Relation.ReflTransGen (pop_step R head σ) m n :=
  Relation.church_rosser (fun _ _ _ => pop_step_diamond R head σ) hl hm

/-- A cursor configuration is terminal when its selected outgoing graph has no legal cycle. -/
def terminal (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    (k : Cursor V) : Prop :=
  ∀ c : Finset V, ¬ IsCycle R (next head σ k) c

private theorem terminal_run_eq (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) {k l : Cursor V} (hk : terminal R head σ k)
    (h : Relation.ReflTransGen (pop_step R head σ) k l) : k = l := by
  rcases h.cases_head with h | ⟨m, ⟨c, hc, _⟩, _⟩
  · exact h
  · exact False.elim (hk c hc)

/-- Once a terminal finite run exists, every other finite legal run can continue to that
same terminal cursor. This is a finite statement and assumes no general termination law. -/
theorem pop_run_continues_to_terminal (R : Set V) (head : (v : V) → A v → V)
    (σ : Stacks A) {k l m : Cursor V}
    (hl : Relation.ReflTransGen (pop_step R head σ) k l)
    (hm : Relation.ReflTransGen (pop_step R head σ) k m)
    (htl : terminal R head σ l) : Relation.ReflTransGen (pop_step R head σ) m l := by
  obtain ⟨n, hln, hmn⟩ := pop_step_confluent R head σ hl hm
  have he : l = n := terminal_run_eq R head σ htl hln
  rw [← he] at hmn
  exact hmn

/-- Every finite legal run uses at most as many instructions at each vertex as any
terminal finite run from the same starting cursor. -/
theorem cursor_le_terminal (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l m : Cursor V} (hl : Relation.ReflTransGen (pop_step R head σ) k l)
    (hm : Relation.ReflTransGen (pop_step R head σ) k m)
    (htl : terminal R head σ l) : m ≤ l :=
  pop_run_le R head σ (pop_run_continues_to_terminal R head σ hl hm htl)

/-- Any two terminal results of finite legal cycle popping have exactly the same cursors. -/
theorem terminal_cursor_eq (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l m : Cursor V} (hl : Relation.ReflTransGen (pop_step R head σ) k l)
    (hm : Relation.ReflTransGen (pop_step R head σ) k m)
    (htl : terminal R head σ l) (htm : terminal R head σ m) : l = m := by
  obtain ⟨n, hln, hmn⟩ := pop_step_confluent R head σ hl hm
  exact (terminal_run_eq R head σ htl hln).trans
    (terminal_run_eq R head σ htm hmn).symm

/-- **Terminal top equals.** terminal finite legal runs select the same actual instruction at every vertex. -/
theorem terminal_top_eq (R : Set V) (head : (v : V) → A v → V) (σ : Stacks A)
    {k l m : Cursor V} (hl : Relation.ReflTransGen (pop_step R head σ) k l)
    (hm : Relation.ReflTransGen (pop_step R head σ) k m)
    (htl : terminal R head σ l) (htm : terminal R head σ m) :
    top σ l = top σ m :=
  congrArg (top σ) (terminal_cursor_eq R head σ hl hm htl htm)

end LatticeProb.Graph.CyclePopping
