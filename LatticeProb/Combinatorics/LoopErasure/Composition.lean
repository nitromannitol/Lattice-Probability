/- Concatenation and cycle erasure for chronological loop erasure. A closed excursion
at the endpoint of a walk, whose other vertices avoid the loop-erased path, does not
change the loop erasure. -/
import LatticeProb.Combinatorics.LoopErasure.Basic

/-! Concatenation and cycle erasure for chronological loop erasure. A closed excursion
at the endpoint of a walk, whose other vertices avoid the loop-erased path, does not
change the loop erasure. -/

set_option autoImplicit false

namespace LatticeProb.Combinatorics.LoopErasure

open Quiver

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- The loop Erase cons equals identity.

The complete public statement is
```lean
theorem loopErase_cons_eq {a b c : V} (p : Path a b) (e : Quiver.Hom b c) :
    loopErase (p.cons e) =
      if h : c ∈ (loopErase p).vertices then prefixTo (loopErase p) c h
      else (loopErase p).cons e
```
-/
theorem loopErase_cons_eq {a b c : V} (p : Path a b) (e : Quiver.Hom b c) :
    loopErase (p.cons e) =
      if h : c ∈ (loopErase p).vertices then prefixTo (loopErase p) c h
      else (loopErase p).cons e := rfl

/-- Truncating at the terminal vertex leaves the whole path unchanged.

The complete public statement is
```lean
theorem prefixTo_self {a b : V} (p : Path a b) (hb : b ∈ p.vertices) :
    prefixTo p b hb = p
```
-/
theorem prefixTo_self {a b : V} (p : Path a b) (hb : b ∈ p.vertices) :
    prefixTo p b hb = p := by
  cases p with
  | nil => rfl
  | cons p e => simp [prefixTo]

/-- Appending an arrow whose endpoint differs from the truncation vertex does not affect truncation.

The complete public statement is
```lean
theorem prefixTo_cons_of_ne {a b c : V} (p : Path a b) (e : Quiver.Hom b c) {v : V}
    (hv : v ∈ (p.cons e).vertices) (hne : c ≠ v) (hv' : v ∈ p.vertices) :
    prefixTo (p.cons e) v hv = prefixTo p v hv'
```
-/
theorem prefixTo_cons_of_ne {a b c : V} (p : Path a b) (e : Quiver.Hom b c) {v : V}
    (hv : v ∈ (p.cons e).vertices) (hne : c ≠ v) (hv' : v ∈ p.vertices) :
    prefixTo (p.cons e) v hv = prefixTo p v hv' := by
  simp only [prefixTo, dif_neg hne]

/-- Vertex membership in a concatenation is membership in either component path.

The complete public statement is
```lean
theorem mem_vertices_comp {a b c : V} (L : Path a b) (r : Path b c) (x : V) :
    x ∈ (L.comp r).vertices ↔ x ∈ L.vertices ∨ x ∈ r.vertices
```
-/
theorem mem_vertices_comp {a b c : V} (L : Path a b) (r : Path b c) (x : V) :
    x ∈ (L.comp r).vertices ↔ x ∈ L.vertices ∨ x ∈ r.vertices := by
  induction r with
  | nil =>
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · have hx : x = b := by simpa using h
          rw [hx]
          exact Quiver.Path.end_mem_vertices L
  | cons r f ih =>
      simp only [show L.comp (r.cons f) = (L.comp r).cons f from rfl,
        Quiver.Path.mem_vertices_cons, ih]
      tauto

/-- If the truncation vertex avoids the first path, truncation acts only on the second path.

The complete public statement is
```lean
theorem prefixTo_comp_of_not_mem {a v : V} (L : Path a v) {u w : V} (r : Path v u)
    (hwL : w ∉ L.vertices) (hwr : w ∈ r.vertices) (hw : w ∈ (L.comp r).vertices) :
    prefixTo (L.comp r) w hw = L.comp (prefixTo r w hwr)
```
-/
theorem prefixTo_comp_of_not_mem {a v : V} (L : Path a v) {u w : V} (r : Path v u)
    (hwL : w ∉ L.vertices) (hwr : w ∈ r.vertices) (hw : w ∈ (L.comp r).vertices) :
    prefixTo (L.comp r) w hw = L.comp (prefixTo r w hwr) := by
  induction r with
  | nil =>
      have hwv : w = v := by simpa using hwr
      exact (hwL (by rw [hwv]; exact Quiver.Path.end_mem_vertices L)).elim
  | @cons m n r f ih =>
      show prefixTo ((L.comp r).cons f) w hw = L.comp (prefixTo (r.cons f) w hwr)
      by_cases hu : n = w
      · subst hu
        rw [prefixTo_self, prefixTo_self]
        rfl
      · have hw0 : w ∈ ((L.comp r).cons f).vertices := hw
        have hw' : w ∈ (L.comp r).vertices :=
          ((Quiver.Path.mem_vertices_cons _ _).mp hw0).resolve_right (Ne.symm hu)
        have hwr' : w ∈ r.vertices :=
          ((Quiver.Path.mem_vertices_cons _ _).mp hwr).resolve_right (Ne.symm hu)
        rw [prefixTo_cons_of_ne (L.comp r) f hw hu hw',
          prefixTo_cons_of_ne r f hwr hu hwr', ih hwr' hw']

/-- Truncating a simple path at its starting vertex yields the empty path.

The complete public statement is
```lean
theorem prefixTo_start_eq_nil {a x : V} (r : Path a x) (hn : r.vertices.Nodup)
    (h : a ∈ r.vertices) : prefixTo r a h = .nil
```
-/
theorem prefixTo_start_eq_nil {a x : V} (r : Path a x) (hn : r.vertices.Nodup)
    (h : a ∈ r.vertices) : prefixTo r a h = .nil := by
  induction r with
  | nil => rfl
  | @cons m n r f ih =>
      have hy := (List.nodup_concat r.vertices n).mp hn
      have hne : n ≠ a := by
        intro hna
        apply hy.1
        rw [hna]
        exact Quiver.Path.start_mem_vertices r
      rw [prefixTo_cons_of_ne r f h hne (Quiver.Path.start_mem_vertices r)]
      exact ih hy.2 (Quiver.Path.start_mem_vertices r)

/-- Truncating a concatenation at the second path’s simple starting vertex recovers the first path.

The complete public statement is
```lean
theorem prefixTo_comp_start {a v x : V} (L : Path a v) (r : Path v x)
    (hn : r.vertices.Nodup) (h : v ∈ (L.comp r).vertices) :
    prefixTo (L.comp r) v h = L
```
-/
theorem prefixTo_comp_start {a v x : V} (L : Path a v) (r : Path v x)
    (hn : r.vertices.Nodup) (h : v ∈ (L.comp r).vertices) :
    prefixTo (L.comp r) v h = L := by
  induction r with
  | nil => exact prefixTo_self L h
  | @cons m n r f ih =>
      have hy := (List.nodup_concat r.vertices n).mp hn
      have hne : n ≠ v := by
        intro hnv
        apply hy.1
        rw [hnv]
        exact Quiver.Path.start_mem_vertices r
      have hL : v ∈ (L.comp r).vertices :=
        (mem_vertices_comp L r v).mpr (Or.inl (Quiver.Path.end_mem_vertices L))
      show prefixTo ((L.comp r).cons f) v h = L
      rw [prefixTo_cons_of_ne (L.comp r) f h hne hL]
      exact ih hy.2 hL

/-- Loop erasure of a concatenation whose second piece meets the loop-erased first piece
only at its starting vertex is the concatenation of the loop erasures. -/
theorem loopErase_comp_of_fresh {a v u : V} (p : Path a v) (q : Path v u)
    (hq : ∀ x ∈ q.vertices, x ∈ (loopErase p).vertices → x = v) :
    loopErase (p.comp q) = (loopErase p).comp (loopErase q) := by
  induction q with
  | nil => rfl
  | @cons m n q e ih =>
      have ih' := ih fun z hz hzL =>
        hq z ((Quiver.Path.mem_vertices_cons q e).mpr (Or.inl hz)) hzL
      show loopErase ((p.comp q).cons e) = (loopErase p).comp (loopErase (q.cons e))
      rw [loopErase_cons_eq (p.comp q) e, ih', loopErase_cons_eq q e]
      by_cases hnL : n ∈ (loopErase p).vertices
      · have hnv : n = v := hq n ((Quiver.Path.mem_vertices_cons q e).mpr (Or.inr rfl)) hnL
        subst n
        have hLr : v ∈ ((loopErase p).comp (loopErase q)).vertices :=
          (mem_vertices_comp (loopErase p) (loopErase q) v).mpr
            (Or.inl (Quiver.Path.end_mem_vertices (loopErase p)))
        rw [dif_pos hLr, dif_pos (Quiver.Path.start_mem_vertices (loopErase q)),
          prefixTo_comp_start (loopErase p) (loopErase q) (loopErase_vertices_nodup q) hLr,
          prefixTo_start_eq_nil (loopErase q) (loopErase_vertices_nodup q)
            (Quiver.Path.start_mem_vertices (loopErase q))]
        rfl
      · by_cases hnr : n ∈ (loopErase q).vertices
        · have hmem : n ∈ ((loopErase p).comp (loopErase q)).vertices :=
            (mem_vertices_comp (loopErase p) (loopErase q) n).mpr (Or.inr hnr)
          rw [dif_pos hmem, dif_pos hnr,
            prefixTo_comp_of_not_mem (loopErase p) (loopErase q) hnL hnr hmem]
        · have hnmem : n ∉ ((loopErase p).comp (loopErase q)).vertices := fun h =>
            ((mem_vertices_comp (loopErase p) (loopErase q) n).mp h).elim hnL hnr
          rw [dif_neg hnmem, dif_neg hnr]
          rfl

omit [DecidableEq V] in
/-- The equals nil of absence of repetitions loop identity.

The complete public statement is
```lean
theorem eq_nil_of_nodup_loop {v : V} (t : Path v v) (hn : t.vertices.Nodup) : t = .nil
```
-/
theorem eq_nil_of_nodup_loop {v : V} (t : Path v v) (hn : t.vertices.Nodup) : t = .nil := by
  cases t with
  | nil => rfl
  | cons r f =>
      exact absurd (Quiver.Path.start_mem_vertices r)
        ((List.nodup_concat r.vertices _).mp hn).1

/-- Cycle erasure: a closed loop at the endpoint `v` of `p`, whose vertices other than `v`
avoid the loop-erased path of `p`, leaves the loop erasure unchanged. -/
theorem loopErase_comp_loop {a v : V} (p : Path a v) (c : Path v v)
    (hc : ∀ x ∈ c.vertices, x ∈ (loopErase p).vertices → x = v) :
    loopErase (p.comp c) = loopErase p := by
  rw [loopErase_comp_of_fresh p c hc,
    eq_nil_of_nodup_loop (loopErase c) (loopErase_vertices_nodup c)]
  rfl

/-- Equal retained prefixes give equal loop erasures after the same suffix. -/
theorem loopErase_comp_congr {a b c : V} (p₁ p₂ : Path a b) (q : Path b c)
    (h : loopErase p₁ = loopErase p₂) :
    loopErase (p₁.comp q) = loopErase (p₂.comp q) := by
  induction q with
  | nil => exact h
  | cons q e ih =>
    rw [Path.comp_cons, Path.comp_cons, loopErase_cons_eq, loopErase_cons_eq, ih]

/-- **Loop erase comp loop comp.** A closed excursion can be deleted before processing any remaining suffix. -/
theorem loopErase_comp_loop_comp {a b d : V} (p : Path a b) (c : Path b b)
    (q : Path b d) (hc : ∀ x ∈ c.vertices, x ∈ (loopErase p).vertices → x = b) :
    loopErase ((p.comp c).comp q) = loopErase (p.comp q) :=
  loopErase_comp_congr (p.comp c) p q (loopErase_comp_loop p c hc)

end LatticeProb.Combinatorics.LoopErasure
