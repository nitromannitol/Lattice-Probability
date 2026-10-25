module

/-
Chronological loop erasure adapted from Scott Armstrong’s finite-avalanches formalization.
The namespace is changed for reuse; the recursive algorithm retains each original arrow.
-/
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Tactic

@[expose] public section

/-! Chronological loop erasure on endpoint-indexed walks. Quiver arrows are
retained, so a surviving edge keeps its original copy, even for parallel edges. -/

set_option autoImplicit false

namespace LatticeProb.Combinatorics.LoopErasure

open Quiver

variable {V : Type*} [Quiver V] [DecidableEq V]

/-- Truncate at the last occurrence of a vertex. On a simple retained path
this is its unique occurrence. The output retains the original arrows. -/
def prefixTo {a : V} : {b : V} → (p : Path a b) → (v : V) → v ∈ p.vertices → Path a v
  | _, .nil, v, hv => by
      have h : v = a := by simpa using hv
      subst v
      exact .nil
  | b, .cons p e, v, hv =>
      if h : b = v then h ▸ p.cons e
      else prefixTo p v ((Quiver.Path.mem_vertices_cons p e).mp hv |>.resolve_right (Ne.symm h))

/-- Online chronological loop erasure: visit vertices in their original order,
retain new arrows, and erase the retained suffix whenever a vertex is revisited. -/
def loopErase {a : V} : {b : V} → Path a b → Path a b
  | _, .nil => .nil
  | b, .cons p e =>
      let q := loopErase p
      if h : b ∈ q.vertices then prefixTo q b h else q.cons e

/-- Truncating a path at a visited vertex produces a vertex list that is a sublist of the original vertex list.

The complete public statement is
```lean
theorem prefixTo_vertices_sublist {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices) :
    (prefixTo p v hv).vertices.Sublist p.vertices
```
-/
theorem prefixTo_vertices_sublist {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices) :
    (prefixTo p v hv).vertices.Sublist p.vertices := by
  induction p with
  | nil =>
      have h : v = a := by simpa using hv
      subst v
      simp [prefixTo]
  | @cons b c p e ih =>
      by_cases h : c = v
      · subst v
        simp [prefixTo]
      · simp only [prefixTo, dif_neg h]
        exact (ih _).trans (by simp [Quiver.Path.vertices_cons])

/-- Truncation preserves absence of repeated vertices.

The complete public statement is
```lean
theorem prefixTo_vertices_nodup {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices)
    (hp : p.vertices.Nodup) : (prefixTo p v hv).vertices.Nodup
```
-/
theorem prefixTo_vertices_nodup {a b : V} (p : Path a b) (v : V) (hv : v ∈ p.vertices)
    (hp : p.vertices.Nodup) : (prefixTo p v hv).vertices.Nodup :=
  hp.sublist (prefixTo_vertices_sublist p v hv)

/-- The vertices surviving chronological loop erasure form a sublist of the original vertices.

The complete public statement is
```lean
theorem loopErase_vertices_sublist {a b : V} (p : Path a b) :
    (loopErase p).vertices.Sublist p.vertices
```
-/
theorem loopErase_vertices_sublist {a b : V} (p : Path a b) :
    (loopErase p).vertices.Sublist p.vertices := by
  induction p with
  | nil => simp [loopErase]
  | @cons b c p e ih =>
      by_cases h : c ∈ (loopErase p).vertices
      · simp only [loopErase, dif_pos h]
        exact (prefixTo_vertices_sublist _ _ h).trans
          (ih.trans (by simp [Quiver.Path.vertices_cons]))
      · simp only [loopErase, dif_neg h, Quiver.Path.vertices_cons, List.concat_eq_append]
        exact ih.append (List.Sublist.refl [c])

/-- Chronological loop erasure produces a path without repeated vertices.

The complete public statement is
```lean
theorem loopErase_vertices_nodup {a b : V} (p : Path a b) : (loopErase p).vertices.Nodup
```
-/
theorem loopErase_vertices_nodup {a b : V} (p : Path a b) : (loopErase p).vertices.Nodup := by
  induction p with
  | nil => simp [loopErase]
  | @cons b c p e ih =>
      by_cases h : c ∈ (loopErase p).vertices
      · simp only [loopErase, dif_pos h]
        exact prefixTo_vertices_nodup _ _ h ih
      · simp only [loopErase, dif_neg h, Quiver.Path.vertices_cons]
        exact ih.concat h

/-- A path without repeated vertices is unchanged by chronological loop erasure.

The complete public statement is
```lean
theorem loopErase_eq_self {a b : V} (p : Path a b) (hp : p.vertices.Nodup) : loopErase p = p
```
-/
theorem loopErase_eq_self {a b : V} (p : Path a b) (hp : p.vertices.Nodup) : loopErase p = p := by
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
      have hpair : c ∉ p.vertices ∧ p.vertices.Nodup :=
        (List.nodup_concat p.vertices c).mp hp
      rw [loopErase, ih hpair.2, dif_neg hpair.1]


/-- Chronological loop erasure preserves the initial vertex.

The complete public statement is
```lean
theorem loopErase_head {a b : V} (p : Path a b) :
    (loopErase p).vertices.head? = some a
```
-/
@[simp] theorem loopErase_head {a b : V} (p : Path a b) :
    (loopErase p).vertices.head? = some a := Quiver.Path.vertices_head? _

/-- Chronological loop erasure preserves the terminal vertex.

The complete public statement is
```lean
theorem loopErase_terminal {a b : V} (p : Path a b) :
    (loopErase p).vertices.getLast (Quiver.Path.vertices_ne_nil _) = b
```
-/
@[simp] theorem loopErase_terminal {a b : V} (p : Path a b) :
    (loopErase p).vertices.getLast (Quiver.Path.vertices_ne_nil _) = b :=
  Quiver.Path.vertices_getLast _ _

/-- **The erased path has no more arrows than the original path.**

The complete public statement is
```lean
theorem loopErase_length_le {a b : V} (p : Path a b) : (loopErase p).length ≤ p.length
```
-/
theorem loopErase_length_le {a b : V} (p : Path a b) : (loopErase p).length ≤ p.length := by
  have h := (loopErase_vertices_sublist p).length_le
  simp only [Quiver.Path.vertices_length] at h
  omega

/-- The quiver of individual unoriented edge copies with their actual endpoints. -/
abbrev copiedQuiver {E : Type*} (ends : E → V × V) : Quiver V where
  Hom x y := {e : E // (ends e = (x, y)) ∨ (ends e = (y, x))}

end LatticeProb.Combinatorics.LoopErasure
