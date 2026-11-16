import LatticeProb.Topology.JordanDiskIntersectionBoundary
import Mathlib.Analysis.Convex.StrictConvexSpace
import LatticeProb.Topology.PolygonalChain

/-! # Chords in embedded disks -/

open Set Metric Topology

namespace LatticeProb.Topology

/-- Any two distinct points of an embedded closed disk are joined by a compact connected
set whose remaining points lie in its interior. -/
theorem exists_compact_connected_chord_of_homeomorph_closedDisk {B : Set ℂ} (e : closedBall (0 : ℂ) 1 ≃ₜ B)
    {x y : ℂ} (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) :
    ∃ Q : Set ℂ, IsCompact Q ∧ IsConnected Q ∧ x ∈ Q ∧ y ∈ Q ∧
      Q ⊆ B ∧ Q \ {x, y} ⊆ interior B := by
  let a := e.symm ⟨x, hx⟩
  let b := e.symm ⟨y, hy⟩
  have hab : (a : ℂ) ≠ (b : ℂ) := by
    intro h
    have he := congrArg (fun z : closedBall (0 : ℂ) 1 => (e z : ℂ)) (Subtype.ext h)
    apply hxy
    simpa only [a, b, Homeomorph.apply_symm_apply] using he
  let S : Set (closedBall (0 : ℂ) 1) := Subtype.val ⁻¹' segment ℝ (a : ℂ) (b : ℂ)
  have hSimage : Subtype.val '' S = segment ℝ (a : ℂ) (b : ℂ) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, (convex_closedBall (0 : ℂ) 1).segment_subset a.property b.property hz⟩, hz, rfl⟩
  have hSc : IsConnected S := by
    constructor
    · exact ⟨a, left_mem_segment ℝ _ _⟩
    · rw [← IsInducing.subtypeVal.isPreconnected_image, hSimage]
      exact (convex_segment (a : ℂ) (b : ℂ)).isPreconnected
  have hSk : IsCompact S := by
    have hc : IsClosed S := (isCompact_segment (a : ℂ) (b : ℂ)).isClosed.preimage continuous_subtype_val
    exact isCompact_univ.of_isClosed_subset hc (subset_univ S)
  let f : closedBall (0 : ℂ) 1 → ℂ := fun z => e z
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  refine ⟨f '' S, hSk.image hf, hSc.image f hf.continuousOn, ?_, ?_, ?_, ?_⟩
  · exact ⟨a, left_mem_segment ℝ _ _, by simp [f, a]⟩
  · exact ⟨b, right_mem_segment ℝ _ _, by simp [f, b]⟩
  · rintro z ⟨w, _, rfl⟩
    exact (e w).property
  · rintro z ⟨⟨w, hw, rfl⟩, hz⟩
    have hwa : (a : ℂ) ≠ w := by
      intro h
      apply hz
      have he : w = a := Subtype.ext h.symm
      simp [f, he, a]
    have hwb : (b : ℂ) ≠ w := by
      intro h
      apply hz
      have he : w = b := Subtype.ext h.symm
      simp [f, he, b]
    have hwball : (w : ℂ) ∈ ball 0 1 :=
      openSegment_subset_ball_of_ne a.property b.property hab
        (mem_openSegment_of_ne_left_right hwa hwb hw)
    apply LatticeProb.homeomorph_subspace_mem_interior e w
    simpa only [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] using hwball


/-- Two contact points of embedded disks with disjoint interiors can be joined in the
second disk by a compact connected set meeting the first disk only at its endpoints. -/
theorem exists_contact_chord_of_embedded_disks {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    {x y : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hxy : x ≠ y) :
    ∃ Q : Set ℂ, IsCompact Q ∧ IsConnected Q ∧ x ∈ Q ∧ y ∈ Q ∧
      Q ⊆ B ∩ closure Aᶜ ∧ Q ∩ A ⊆ {x, y} := by
  obtain ⟨Q, hQc, hQcon, hxQ, hyQ, hQB, hQint⟩ := exists_compact_connected_chord_of_homeomorph_closedDisk eB hx.2 hy.2 hxy
  have hAB : Disjoint A (interior B) := by
    rw [← LatticeProb.closure_interior_of_homeomorph_closedDisk eA]
    exact hdis.closure_left isOpen_interior
  have hfront := (LatticeProb.embedded_disks_inter_frontiers eA eB hdis).2.1
  have hxcl : x ∈ closure Aᶜ := by
    have h := hfront hx
    rw [frontier_eq_closure_inter_closure] at h
    exact h.2
  have hycl : y ∈ closure Aᶜ := by
    have h := hfront hy
    rw [frontier_eq_closure_inter_closure] at h
    exact h.2
  refine ⟨Q, hQc, hQcon, hxQ, hyQ, ?_, ?_⟩
  · intro z hz
    refine ⟨hQB hz, ?_⟩
    by_cases hxz : z = x
    · simpa only [hxz] using hxcl
    by_cases hyz : z = y
    · simpa only [hyz] using hycl
    apply subset_closure
    intro hzA
    exact (disjoint_left.mp hAB) hzA (hQint ⟨hz, by simp [hxz, hyz]⟩)
  · rintro z ⟨hzQ, hzA⟩
    by_contra hz
    exact (disjoint_left.mp hAB) hzA (hQint ⟨hzQ, hz⟩)

end LatticeProb.Topology
