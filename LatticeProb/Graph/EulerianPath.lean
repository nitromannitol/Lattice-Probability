/-
Moved from nitromannitol/rotor-23, `Rotor/Support/EulerPath.lean`, Apache-2.0;
copyright 2026 Ahmed Bou-Rabee and Yuval Peres.  There the file is the
combinatorial core of the proof of `lem:decreasing-positions` (i)
(`rotor.tex:899-928`), but every declaration is stated for a bare finite set
of directed edges on an arbitrary type `V`, with no reference to the rotor
mechanism, so it is moved here unchanged, with only the namespace renamed.
-/
import Mathlib

/-!
# A path from a set to a vertex of excess in-degree

If every vertex outside `S ∪ {y}` has in-degree at most out-degree in a
finite set of directed edges `E`, while `y ∉ S` has in-degree exceeding its
out-degree, then `E` contains a path from `S` to `y` avoiding `S` after its
first vertex (`exists_epath`).  The proof induces on `|E|`: an in-edge of `y`
is removed, moving the excess to its tail, until that tail lies in `S`.
-/

open Finset

namespace LatticeProb.Graph

variable {V : Type*} [DecidableEq V]

/-- In-degree of `v` in the edge set `E`. -/
def indeg (E : Finset (V × V)) (v : V) : ℕ := (E.filter (fun e => e.2 = v)).card

/-- Out-degree of `v` in the edge set `E`. -/
def outdeg (E : Finset (V × V)) (v : V) : ℕ := (E.filter (fun e => e.1 = v)).card

/-- A path of `E` from `S` to `y`: distinct vertices, first in `S`, the rest
outside `S`, consecutive pairs in `E`. -/
structure IsEPath (E : Finset (V × V)) (S : Finset V) (l : List V) (y : V) : Prop where
  nodup : l.Nodup
  two_le : 2 ≤ l.length
  head_mem : ∀ h : 0 < l.length, l.get ⟨0, h⟩ ∈ S
  tail_not_mem : ∀ (i : ℕ) (h : i < l.length), 1 ≤ i → l.get ⟨i, h⟩ ∉ S
  last : l.getLast? = some y
  chain : l.IsChain (fun u v => (u, v) ∈ E)

/-- Erasing an edge `e` into `v` drops `v`'s in-degree by one. -/
theorem indeg_erase (E : Finset (V × V)) (e : V × V) (he : e ∈ E) (v : V) :
    indeg (E.erase e) v = indeg E v - (if e.2 = v then 1 else 0) := by
  unfold indeg
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨he, h⟩)]
  · have : e ∉ E.filter (fun e => e.2 = v) := fun hm => h (Finset.mem_filter.1 hm).2
    rw [Finset.erase_eq_of_notMem this]
    simp

/-- Erasing an edge `e` out of `v` drops `v`'s out-degree by one. -/
theorem outdeg_erase (E : Finset (V × V)) (e : V × V) (he : e ∈ E) (v : V) :
    outdeg (E.erase e) v = outdeg E v - (if e.1 = v then 1 else 0) := by
  unfold outdeg
  rw [Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨he, h⟩)]
  · have : e ∉ E.filter (fun e => e.1 = v) := fun hm => h (Finset.mem_filter.1 hm).2
    rw [Finset.erase_eq_of_notMem this]
    simp

omit [DecidableEq V] in
/-- An `E`-path is an `E'`-path for `E ⊆ E'`. -/
theorem IsEPath.mono {E E' : Finset (V × V)} (hEE : E ⊆ E') {S : Finset V} {l : List V} {y : V}
    (h : IsEPath E S l y) : IsEPath E' S l y :=
  { h with chain := h.chain.imp (fun _ _ hm => hEE hm) }

omit [DecidableEq V] in
/-- Cutting an `E`-path at the first occurrence of a vertex `y ∉ S` gives an
`E`-path to `y`. -/
theorem IsEPath.cut {E : Finset (V × V)} {S : Finset V} {l : List V} {u : V}
    (h : IsEPath E S l u) (y : V) (hy : y ∉ S) (hyl : y ∈ l) :
    ∃ l', IsEPath E S l' y := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hyl
  refine ⟨s ++ [y], ?_⟩
  have heq : s ++ y :: t = (s ++ [y]) ++ t := by simp
  have hsub : List.Sublist (s ++ [y]) (s ++ y :: t) := by
    rw [heq]; exact List.sublist_append_left _ _
  have hs : s ≠ [] := by
    rintro rfl
    have := h.head_mem (by simp)
    simp at this
    exact hy this
  refine {
    nodup := h.nodup.sublist hsub
    two_le := by
      rw [List.length_append, List.length_singleton]
      have := List.length_pos_of_ne_nil hs
      omega
    head_mem := by
      intro h0
      have h0' : 0 < (s ++ y :: t).length := by simp
      have := h.head_mem h0'
      rwa [List.get_eq_getElem, List.getElem_append_left (List.length_pos_of_ne_nil hs)] at this ⊢
    tail_not_mem := by
      intro i hi hi1
      have hi' : i < (s ++ y :: t).length := by
        rw [List.length_append, List.length_singleton] at hi
        rw [List.length_append, List.length_cons]; omega
      have := h.tail_not_mem i hi' hi1
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.getElem_of_eq heq, List.getElem_append_left hi] at this
      exact this
    last := by simp
    chain := by
      have := h.chain
      rw [heq, List.isChain_append] at this
      exact this.1 }

omit [DecidableEq V] in
/-- Appending a new vertex `y ∉ S` joined by an edge of `E`. -/
theorem IsEPath.append {E : Finset (V × V)} {S : Finset V} {l : List V} {u : V}
    (h : IsEPath E S l u) (y : V) (hy : y ∉ S) (hyl : y ∉ l) (he : (u, y) ∈ E) :
    IsEPath E S (l ++ [y]) y := by
  have hl : l ≠ [] := by rintro rfl; have := h.two_le; simp at this
  refine {
    nodup := by
      rw [List.nodup_append]
      exact ⟨h.nodup, List.nodup_singleton _, fun a ha b hb hab => by
        rw [List.mem_singleton] at hb; rw [hab, hb] at ha; exact hyl ha⟩
    two_le := by rw [List.length_append, List.length_singleton]; have := h.two_le; omega
    head_mem := by
      intro h0
      have h0' : 0 < l.length := List.length_pos_of_ne_nil hl
      have := h.head_mem h0'
      simp only [List.get_eq_getElem] at this ⊢
      rwa [List.getElem_append_left h0']
    tail_not_mem := by
      intro i hi hi1
      simp only [List.get_eq_getElem]
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge i l.length with hlt | hge
      · rw [List.getElem_append_left hlt]
        have := h.tail_not_mem i hlt hi1
        simpa only [List.get_eq_getElem] using this
      · have hi' : i = l.length := by omega
        subst hi'
        rw [List.getElem_append_right le_rfl]
        simpa using hy
    last := by simp
    chain := by
      rw [List.isChain_append]
      refine ⟨h.chain, List.IsChain.singleton _, fun a ha b hb => ?_⟩
      rw [h.last, Option.mem_def, Option.some_inj] at ha
      rw [List.head?_singleton, Option.mem_def, Option.some_inj] at hb
      subst ha; subst hb; exact he }

/-- **The path lemma.**  If every vertex outside `S ∪ {y}` is balanced
(out-degree at most in-degree) in the finite edge set `E`, while `y ∉ S` has
strictly more in-degree than out-degree, then `E` contains a path from `S` to
`y`. -/
theorem exists_epath (E : Finset (V × V)) (S : Finset V) (y : V) (hy : y ∉ S)
    (hbal : ∀ v, v ∉ S → v ≠ y → outdeg E v ≤ indeg E v)
    (hexc : outdeg E y < indeg E y) :
    ∃ l : List V, IsEPath E S l y := by
  induction E using Finset.strongInduction generalizing y with
  | H E ih =>
    -- an in-edge of `y`
    have hpos : 0 < indeg E y := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter] at he
    obtain ⟨heE, hey⟩ := he
    obtain ⟨u, y'⟩ := e
    simp only at hey
    rw [hey] at heE
    clear hey y'
    by_cases hu : u ∈ S
    · refine ⟨[u, y], ?_⟩
      have huy : u ≠ y := fun h => hy (h ▸ hu)
      exact {
        nodup := by simp [huy]
        two_le := by simp
        head_mem := fun _ => hu
        tail_not_mem := by
          intro i hi hi1
          have hi2 : i < 2 := by simpa using hi
          interval_cases i
          simpa using hy
        last := rfl
        chain := by simpa using heE }
    · -- `u ∉ S`: remove the edge; the excess moves to `u` (or stays, for a loop)
      have hE' : E.erase (u, y) ⊂ E := Finset.erase_ssubset heE
      by_cases huy : u = y
      · subst huy
        have hbal' : ∀ v, v ∉ S → v ≠ u →
            outdeg (E.erase (u, u)) v ≤ indeg (E.erase (u, u)) v := by
          intro v hv hvu
          rw [indeg_erase _ _ heE, outdeg_erase _ _ heE]
          simp only [Ne.symm hvu, if_false, Nat.sub_zero]
          exact hbal v hv hvu
        have hexc' : outdeg (E.erase (u, u)) u < indeg (E.erase (u, u)) u := by
          rw [indeg_erase _ _ heE, outdeg_erase _ _ heE]
          simp only [if_true]
          have h1 : 0 < outdeg E u :=
            Finset.card_pos.2 ⟨(u, u), Finset.mem_filter.2 ⟨heE, rfl⟩⟩
          omega
        obtain ⟨l, hl⟩ := ih _ hE' u hu hbal' hexc'
        exact ⟨l, hl.mono (Finset.erase_subset _ _)⟩
      · have hbal' : ∀ v, v ∉ S → v ≠ u →
            outdeg (E.erase (u, y)) v ≤ indeg (E.erase (u, y)) v := by
          intro v hv hvu
          rw [indeg_erase _ _ heE, outdeg_erase _ _ heE]
          simp only [Ne.symm hvu, if_false, Nat.sub_zero]
          by_cases hvy : v = y
          · subst hvy
            simp only [if_true]
            omega
          · simp only [Ne.symm hvy, if_false, Nat.sub_zero]
            exact hbal v hv hvy
        have hexc' : outdeg (E.erase (u, y)) u < indeg (E.erase (u, y)) u := by
          rw [indeg_erase _ _ heE, outdeg_erase _ _ heE]
          simp only [Ne.symm huy, if_false, Nat.sub_zero, if_true]
          have := hbal u hu huy
          have h1 : 0 < outdeg E u :=
            Finset.card_pos.2 ⟨(u, y), Finset.mem_filter.2 ⟨heE, rfl⟩⟩
          omega
        obtain ⟨l, hl⟩ := ih _ hE' u hu hbal' hexc'
        have hl' := hl.mono (Finset.erase_subset _ _)
        by_cases hyl : y ∈ l
        · exact hl'.cut y hy hyl
        · exact ⟨l ++ [y], hl'.append y hy hyl heE⟩

end LatticeProb.Graph
