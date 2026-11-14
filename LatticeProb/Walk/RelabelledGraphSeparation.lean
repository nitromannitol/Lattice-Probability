import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Chain
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! # Graph separation under relabelling -/

set_option autoImplicit false

open Set MatedCRTHarmonic.HarmonicInfinity

namespace LatticeProb

/-- The preimage of a separating set separates the preimages of its targets. -/
theorem graphSeparates_preimage_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {U A B : Set W} (h : GraphSeparates H U A B) :
    GraphSeparates G (f ⁻¹' U) (f ⁻¹' A) (f ⁻¹' B) := by
  intro a ha b hb p
  obtain ⟨y, hy, hU⟩ := h (f a) ha (f b) hb (p.map f)
  rw [SimpleGraph.Walk.support_map] at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact ⟨x, hx, hU⟩

/-- Graph isomorphisms preserve separation of arbitrary vertex sets. -/
theorem graphSeparates_preimage_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (U A B : Set W) :
    GraphSeparates G (e ⁻¹' U) (e ⁻¹' A) (e ⁻¹' B) ↔ GraphSeparates H U A B := by
  constructor
  · intro h
    have hh := graphSeparates_preimage_of_hom e.symm.toHom h
    simpa only [Set.preimage_preimage, Function.comp_def, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
      RelIso.apply_symm_apply,
      Set.preimage_id, Set.preimage_id'] using hh
  · exact graphSeparates_preimage_of_hom e.toHom

end LatticeProb
