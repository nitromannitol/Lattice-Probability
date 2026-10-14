/-
# Finite polygonal chains in real normed spaces

The carrier of a vertex list is the union of its consecutive closed segments.
Open connected sets admit such chains between any two prescribed points.

Adapted from Álvaro Begué's `Schoenflies/PolyPath.lean` in
`alonamaloh/schoenflies-lean`, commit `05a43d29cde026618777db3d4e4316204ccca237`.
The plane-specific proofs are generalized to real normed spaces. Apache 2.0.
-/
/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected



open Metric Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Ω : Set E} {x y z : E}

/-! ### Segments -/

/-- A closed real segment is compact. -/
theorem isCompact_segment (x y : E) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def polygonalChain : List E → Set E
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ polygonalChain (v :: rest)

/-- The empty vertex list has empty trace. -/
@[simp] theorem polygonal_chain_nil : polygonalChain ([] : List E) = ∅ := rfl

/-- A singleton vertex list has singleton trace. -/
@[simp] theorem polygonal_chain_singleton (v : E) : polygonalChain [v] = {v} := rfl

/-- The trace consists of the first segment and the remaining chain. -/
@[simp] theorem polygonal_chain_cons_cons (u v : E) (rest : List E) :
    polygonalChain (u :: v :: rest) = segment ℝ u v ∪ polygonalChain (v :: rest) := rfl

/-- A nonempty vertex list has a nonempty trace. -/
theorem polygonal_chain_nonempty : ∀ {vs : List E}, vs ≠ [] → (polygonalChain vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

/-- Every finite polygonal chain has compact trace. -/
theorem isCompact_polygonal_chain : ∀ vs : List E, IsCompact (polygonalChain vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [polygonal_chain_cons_cons]
    exact (isCompact_segment u v).union (isCompact_polygonal_chain (v :: rest))

/-- Every vertex lies on the carrier. -/
theorem mem_polygonal_chain_of_mem : ∀ {vs : List E} {v : E}, v ∈ vs → v ∈ polygonalChain vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_polygonal_chain_of_mem h)

/-- The first vertex belongs to the trace of a nonempty chain. -/
theorem head_mem_polygonal_chain {vs : List E} (h : vs ≠ []) : vs.head h ∈ polygonalChain vs :=
  mem_polygonal_chain_of_mem (List.head_mem h)

/-- The last vertex belongs to the trace of a nonempty chain. -/
theorem getLast_mem_polygonal_chain {vs : List E} (h : vs ≠ []) : vs.getLast h ∈ polygonalChain vs :=
  mem_polygonal_chain_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex. -/
theorem isConnected_polygonal_chain : ∀ {vs : List E}, vs ≠ [] → IsConnected (polygonalChain vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [polygonal_chain_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_polygonal_chain (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_polygonal_chain (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment. -/
theorem polygonal_chain_concat : ∀ {vs : List E} (h : vs ≠ []) (z : E),
    polygonalChain (vs ++ [z]) = polygonalChain vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, polygonal_chain_cons_cons, polygonal_chain_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, polygonal_chain_cons_cons]
    rw [← List.cons_append, polygonal_chain_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

/-- **Polygonal connectedness.** Two points of an open preconnected set can be joined inside it by a finite
polygonal chain. No path-connectedness assumption is needed. -/
theorem exists_polygonal_chain_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List E, ∃ h : vs ≠ [], polygonalChain vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  -- `R` is the set of points reachable from `x` by a polygonal path inside `Ω`.
  set R : Set E :=
    {w ∈ Ω | ∃ vs : List E, ∃ h : vs ≠ [], polygonalChain vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  -- Extending a path by a segment inside a convex subset of `Ω` keeps it inside `Ω`. Applied
  -- to a ball this makes `R` open, and applied in the other direction makes `Ω \ R` open.
  have key : ∀ C : Set E, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List E, ∃ h : vs ≠ [], polygonalChain vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List E, ∃ h : vs ≠ [], polygonalChain vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [polygonal_chain_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    -- A path to `z` runs back to `w` through the same ball, so `w ∈ R` after all.
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  -- `R` is nonempty, open and closed in the preconnected `Ω`, so `R = Ω`.
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

end LatticeProb.Topology
