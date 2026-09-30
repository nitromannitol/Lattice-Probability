/-
Moved from nitromannitol/rotor-23, `Rotor/Support/Konig.lean`, Apache-2.0;
copyright 2026 Ahmed Bou-Rabee and Yuval Peres.  There the file is used in the
proof of `prop:live-recurrence` (`rotor.tex:955-963`), but every declaration
is stated for a bare type `α` and a predicate `P` on `List α`, with no
reference to the rotor model, so it is moved here unchanged, with only the
namespace renamed.
-/
import Mathlib

/-!
# König's lemma for a prefix-closed, finitely branching family

If `P : List α → Prop` is prefix-closed (`hpre`), finitely branching at every
node (`hfin`), and has members of every length (`hlong`), then there is an
infinite sequence `x : ℕ → α` all of whose finite prefixes satisfy `P`
(`konig`).  This is the elementary combinatorial König's lemma for a tree
whose nodes are finite lists: `Extendable P l` says `l` has members of `P`
extending it of every length, and `konigSeq` builds the sequence of nested
extendable prefixes by always choosing an extendable one-step extension
(`Extendable.step`).
-/

namespace LatticeProb.Graph

variable {α : Type*}

/-- `l` has members of `P` extending it of every length. -/
def Extendable (P : List α → Prop) (l : List α) : Prop :=
  ∀ n : ℕ, ∃ q : List α, P q ∧ l <+: q ∧ n ≤ q.length

/-- A prefix-closed predicate holds on every prefix of a member. -/
theorem P_of_prefix (P : List α → Prop) (hpre : ∀ l a, P (l ++ [a]) → P l) :
    ∀ q : List α, P q → ∀ l, l <+: q → P l := by
  intro q
  induction q using List.reverseRecOn with
  | nil =>
    intro hq l hl
    rw [List.prefix_nil] at hl
    exact hl ▸ hq
  | append_singleton q a ih =>
    intro hq l hl
    rcases List.prefix_concat_iff.1 hl with rfl | hl'
    · exact hq
    · exact ih (hpre q a hq) l hl'

/-- An extendable list itself satisfies `P` (via its length-`0`
extension). -/
theorem Extendable.P (P : List α → Prop) (hpre : ∀ l a, P (l ++ [a]) → P l) (l : List α)
    (h : Extendable P l) : P l := by
  obtain ⟨q, hq, hl, -⟩ := h 0
  exact P_of_prefix P hpre q hq l hl

/-- An extendable list has an extendable one-step extension, when it has
finitely many one-step extensions (the pigeonhole step of König's lemma). -/
theorem Extendable.step (P : List α → Prop) (hpre : ∀ l a, P (l ++ [a]) → P l)
    (l : List α) (hfin : Set.Finite {a | P (l ++ [a])}) (h : Extendable P l) :
    ∃ a, Extendable P (l ++ [a]) := by
  by_contra hcon
  simp only [Extendable, not_exists, not_forall, not_and, not_le] at hcon
  -- every child has a bound
  choose N hN using hcon
  -- a common bound over the finitely many children
  obtain ⟨M, hM⟩ : ∃ M, ∀ a, P (l ++ [a]) → N a ≤ M := by
    refine ⟨hfin.toFinset.sup N, fun a ha => Finset.le_sup (f := N) ?_⟩
    rwa [Set.Finite.mem_toFinset]
  obtain ⟨q, hq, hl, hlen⟩ := h (max M (l.length + 1))
  -- `q` properly extends `l`, through some child
  obtain ⟨t, rfl⟩ := hl
  cases t with
  | nil => simp at hlen
  | cons a t =>
    have hchild : P (l ++ [a]) :=
      P_of_prefix P hpre _ hq _ ⟨t, by simp⟩
    have := hN a (l ++ a :: t) hq ⟨t, by simp⟩
    have h1 := hM a hchild
    have h3 := le_max_left M (l.length + 1)
    omega

/-- The sequence of nested extendable prefixes, built by iterating a choice
of extendable one-step extension. -/
noncomputable def konigSeq (P : List α → Prop) (f : ∀ l, Extendable P l → α)
    (hf : ∀ l h, Extendable P (l ++ [f l h])) (h0 : Extendable P []) :
    ℕ → {l : List α // Extendable P l}
  | 0 => ⟨[], h0⟩
  | n + 1 => ⟨(konigSeq P f hf h0 n).1 ++ [f _ (konigSeq P f hf h0 n).2], hf _ _⟩

/-- **König's lemma.**  A prefix-closed, finitely branching predicate on
finite lists with members of every length has an infinite sequence all of
whose finite prefixes are members. -/
theorem konig (P : List α → Prop) (hpre : ∀ l a, P (l ++ [a]) → P l)
    (hfin : ∀ l, Set.Finite {a | P (l ++ [a])}) (hlong : ∀ n, ∃ l, P l ∧ n ≤ l.length) :
    ∃ x : ℕ → α, ∀ n, P ((List.range n).map x) := by
  classical
  have h0 : Extendable P [] := fun n => by
    obtain ⟨l, hl, hn⟩ := hlong n
    exact ⟨l, hl, List.nil_prefix, hn⟩
  have hstep : ∀ l, Extendable P l → ∃ a, Extendable P (l ++ [a]) :=
    fun l h => Extendable.step P hpre l (hfin l) h
  choose f hf using hstep
  refine ⟨fun n => f _ (konigSeq P f hf h0 n).2, fun n => ?_⟩
  have key : ∀ n, (List.range n).map (fun n => f _ (konigSeq P f hf h0 n).2) =
      (konigSeq P f hf h0 n).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.range_succ, List.map_append, ih]; rfl
  rw [key]
  exact Extendable.P P hpre _ (konigSeq P f hf h0 n).2

end LatticeProb.Graph
