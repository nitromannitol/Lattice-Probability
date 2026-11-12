import LatticeProb.Topology.PolygonalParityCoordinates
import LatticeProb.Topology.PolygonalChain

/-!
# Local separation by a closed polygon in the complex plane

A polygonal chain `b = v₀, v₁, …, vₙ = a` in `ℂ`, closed by the edge `[a, b]`, is a closed polygon (not
necessarily simple). Let `e` be an interior point of the closing edge that does not lie on the chain. Then near `e`
the two sides of the closing edge, distinguished by the sign of `Im (conj (b - a) * (z - e))`, cannot be joined by
a preconnected set missing the polygon.

This is the parity separation theorem for closed polygons (`exists_coordinate_local_separation`), transported from
`ℝ × ℝ` to `ℂ` by `Complex.equivRealProdLm`, with the cyclic edge list of the polygon written as the edges of the
chain followed by the closing edge.

* `zip_append_singleton_eq`, `zip_rotate_one_cons`: the cyclic edge list of `u :: rest`.
* `polygonalChain_cons_cons_eq_biUnion`: the trace of a polygonal chain is the union of its edges.
* `exists_closing_edge_separation`: the local separation statement.
-/

open Set Metric ComplexConjugate
open LatticeProb.Topology.PolygonalParity

namespace LatticeProb.Topology

/-- Zipping a list with its tail followed by an extra element appends one pair (last element, extra element). -/
theorem zip_append_singleton_eq {α : Type*} (w : α) :
    ∀ (u : α) (rest : List α),
      (u :: rest).zip (rest ++ [w]) = (u :: rest).zip rest ++ [((u :: rest).getLast (List.cons_ne_nil u rest), w)]
  | u, [] => rfl
  | u, v :: r => by
    rw [List.cons_append, List.zip_cons_cons, zip_append_singleton_eq w v r, List.getLast_cons_cons]
    rfl

/-- The cyclic edge list of `u :: rest`: the consecutive edges followed by the closing edge from the last vertex
back to `u`. -/
theorem zip_rotate_one_cons {α : Type*} (u : α) (rest : List α) :
    (u :: rest).zip ((u :: rest).rotate 1) =
      (u :: rest).zip rest ++ [((u :: rest).getLast (List.cons_ne_nil u rest), u)] := by
  rw [List.rotate_cons_succ, List.rotate_zero, zip_append_singleton_eq]

/-- The trace of a polygonal chain with at least two vertices is the union of its edges. -/
theorem polygonalChain_cons_cons_eq_biUnion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (u v : E) (rest : List E),
      polygonalChain (u :: v :: rest) = ⋃ P ∈ (u :: v :: rest).zip (v :: rest), segment ℝ P.1 P.2
  | u, v, [] => by
    ext z
    simp only [polygonal_chain_cons_cons, polygonal_chain_singleton, List.zip_cons_cons, List.zip_nil_right,
      List.mem_singleton, mem_iUnion, exists_prop, exists_eq_left, mem_union]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact right_mem_segment ℝ u z
    · exact Or.inl
  | u, v, w :: r => by
    have hz : (u :: v :: w :: r).zip (v :: w :: r) = (u, v) :: (v :: w :: r).zip (w :: r) := rfl
    rw [hz, polygonal_chain_cons_cons, polygonalChain_cons_cons_eq_biUnion v w r]
    ext z
    simp only [mem_union, mem_iUnion, List.mem_cons, exists_prop]
    constructor
    · rintro (h | ⟨P, hP, hz⟩)
      · exact ⟨(u, v), Or.inl rfl, h⟩
      · exact ⟨P, Or.inr hP, hz⟩
    · rintro ⟨P, rfl | hP, hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨P, hP, hz⟩

/-- Membership in a segment is preserved and reflected by the real-linear identification `ℂ ≃ ℝ × ℝ`. -/
theorem equivRealProdLm_mem_segment_iff {a b z : ℂ} :
    Complex.equivRealProdLm z ∈ segment ℝ (Complex.equivRealProdLm a) (Complex.equivRealProdLm b) ↔
      z ∈ segment ℝ a b := by
  have h := image_segment ℝ ((Complex.equivRealProdLm : ℂ →ₗ[ℝ] ℝ × ℝ).toAffineMap) a b
  simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] at h
  rw [← h]
  exact Complex.equivRealProdLm.injective.mem_set_image

/-- The trace of a mapped edge list, pulled back to `ℂ`. -/
theorem equivRealProdLm_mem_coordinateEdgeTrace_iff (L : List (ℂ × ℂ)) (z : ℂ) :
    Complex.equivRealProdLm z ∈
        coordinateEdgeTrace (L.map (Prod.map Complex.equivRealProdLm Complex.equivRealProdLm)) ↔
      z ∈ ⋃ P ∈ L, segment ℝ P.1 P.2 := by
  simp only [coordinateEdgeTrace, mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨_, ⟨Q, hQ, rfl⟩, hz⟩
    exact ⟨Q, hQ, equivRealProdLm_mem_segment_iff.1 hz⟩
  · rintro ⟨Q, hQ, hz⟩
    exact ⟨_, ⟨Q, hQ, rfl⟩, equivRealProdLm_mem_segment_iff.2 hz⟩

/-- The coordinate determinant against `b - a`, relative to `e`, is the imaginary part of
`conj (b - a) * (x - e)`. -/
theorem coordinateDet_equivRealProdLm_sub (b a e x : ℂ) :
    coordinateDet (Complex.equivRealProdLm b - Complex.equivRealProdLm a) (Complex.equivRealProdLm x) -
        coordinateDet (Complex.equivRealProdLm b - Complex.equivRealProdLm a) (Complex.equivRealProdLm e) =
      (conj (b - a) * (x - e)).im := by
  simp only [coordinateDet, Complex.equivRealProdLm_apply, Prod.fst_sub, Prod.snd_sub, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

/-- **Local separation by a closed polygon.** Let `b :: rest` be a polygonal chain in `ℂ` with nondegenerate edges,
ending at `a ≠ b`, and close it by the edge `[a, b]`. If `e` is an interior point of the closing edge off the
chain, then some open neighbourhood `U` of `e` has the property: a point of `U` strictly on the left of the closing
edge and a point of `U` strictly on its right are joined by no preconnected set missing the polygon. -/
theorem exists_closing_edge_separation {b a e : ℂ} {rest : List ℂ}
    (hlast : (b :: rest).getLast (List.cons_ne_nil _ _) = a)
    (hnd : ∀ P ∈ (b :: rest).zip rest, P.1 ≠ P.2) (huu : a ≠ b)
    (he : e ∈ openSegment ℝ a b) (heL : e ∉ polygonalChain (b :: rest)) :
    ∃ U : Set ℂ, IsOpen U ∧ e ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      0 < (conj (b - a) * (x - e)).im → (conj (b - a) * (y - e)).im < 0 →
      ∀ S : Set ℂ, IsPreconnected S → x ∈ S → y ∈ S →
        (S ∩ (polygonalChain (b :: rest) ∪ segment ℝ a b)).Nonempty := by
  obtain _ | ⟨v, r⟩ := rest
  · exact absurd hlast.symm huu
  set f := Complex.equivRealProdLm with hf
  set L : List (ℂ × ℂ) := (b :: v :: r).zip (v :: r) with hL
  have hchain : polygonalChain (b :: v :: r) = ⋃ P ∈ L, segment ℝ P.1 P.2 :=
    polygonalChain_cons_cons_eq_biUnion b v r
  have hedges : ((b :: v :: r).map f).zip (((b :: v :: r).map f).rotate 1) =
      L.map (Prod.map f f) ++ (f a, f b) :: [] := by
    rw [← List.map_rotate, List.zip_map, zip_rotate_one_cons, List.map_append, hlast]
    rfl
  have hnd' : ∀ P ∈ ((b :: v :: r).map f).zip (((b :: v :: r).map f).rotate 1), P.1 ≠ P.2 := by
    rw [hedges]
    intro P hP
    rcases List.mem_append.1 hP with hP | hP
    · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hP
      exact fun h => hnd Q hQ (f.injective h)
    · rw [List.mem_singleton] at hP
      subst hP
      exact fun h => huu (f.injective h)
  have hp : f e ∈ openSegment ℝ (f a) (f b) := by
    have h := image_openSegment ℝ ((f : ℂ →ₗ[ℝ] ℝ × ℝ).toAffineMap) a b
    simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] at h
    rw [← h]
    exact mem_image_of_mem _ he
  have h1 : f e ∉ coordinateEdgeTrace (L.map (Prod.map f f)) := by
    rw [equivRealProdLm_mem_coordinateEdgeTrace_iff, ← hchain]
    exact heL
  have h2 : f e ∉ coordinateEdgeTrace ([] : List ((ℝ × ℝ) × (ℝ × ℝ))) := by
    simp [coordinateEdgeTrace]
  obtain ⟨U', hU', heU', hsep⟩ := exists_coordinate_local_separation _ hedges hnd' hp h1 h2
  refine ⟨f ⁻¹' U', hU'.preimage f.toContinuousLinearEquiv.continuous, heU', ?_⟩
  intro x hx y hy hxs hys S hS hxS hyS
  have hdx := coordinateDet_equivRealProdLm_sub b a e x
  have hdy := coordinateDet_equivRealProdLm_sub b a e y
  obtain ⟨-, -, hmeet⟩ := hsep (f x) (f y) hx hy (by rw [← hf] at hdx; linarith)
    (by rw [← hf] at hdy; linarith)
  obtain ⟨_, ⟨s, hsS, rfl⟩, hs⟩ := hmeet (f '' S)
    (hS.image _ f.toContinuousLinearEquiv.continuous.continuousOn) (mem_image_of_mem _ hxS)
    (mem_image_of_mem _ hyS)
  refine ⟨s, hsS, ?_⟩
  rw [hedges] at hs
  simp only [coordinateEdgeTrace, List.mem_append, List.mem_singleton, mem_iUnion, exists_prop] at hs
  obtain ⟨P, hP | rfl, hsP⟩ := hs
  · left
    rw [hchain]
    exact (equivRealProdLm_mem_coordinateEdgeTrace_iff L s).1
      (mem_iUnion₂.2 ⟨P, hP, hsP⟩)
  · right
    exact equivRealProdLm_mem_segment_iff.1 hsP

end LatticeProb.Topology
