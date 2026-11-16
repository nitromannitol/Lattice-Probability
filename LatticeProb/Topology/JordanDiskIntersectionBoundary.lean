import LatticeProb.Topology.EmbeddedDiskConnectedInterior
import LatticeProb.Topology.EmbeddedClosedDiskExterior
import LatticeProb.Topology.JordanCurveClosedSubsetComponents
import LatticeProb.Topology.AreaCurveSharedFrontier

/-! # Intersections of embedded closed disks -/

set_option autoImplicit false

noncomputable section

open Set Metric Bornology
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- A planar embedded closed disk is the closure of its interior. -/
theorem closure_interior_of_homeomorph_closedDisk {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) : closure (interior K) = K := by
  let D : Set (closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ ball 0 1}
  have hD : Subtype.val '' D = ball (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z, ball_subset_closedBall hz⟩, hz, rfl⟩
  have hDdense : ∀ x, x ∈ closure D := by
    intro x
    rw [closure_subtype, hD, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact x.2
  let f : closedBall (0 : ℂ) 1 → ℂ := fun x => e x
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : f '' D ⊆ interior K := by
    rintro _ ⟨x, hx, rfl⟩
    apply homeomorph_subspace_mem_interior e x
    change (x : ℂ) ∈ ball 0 1 at hx
    simpa only [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] using hx
  have hKcompact : IsCompact K := by
    have h : IsCompact (range f) := isCompact_range (continuous_subtype_val.comp e.continuous)
    have hr : range f = K := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (e y).2
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, by simp [f]⟩
    simpa only [hr] using h
  apply Subset.antisymm (closure_minimal interior_subset hKcompact.isClosed)
  intro x hx
  let y := e.symm ⟨x, hx⟩
  have hy : f y ∈ closure (f '' D) :=
    image_closure_subset_closure_image hf ⟨y, hDdense y, rfl⟩
  exact (by simpa [f, y] using (closure_mono hfi hy))

/-- A planar embedded disk has a Jordan frontier. -/
theorem isJordanCurve_frontier_of_homeomorph_closedDisk {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) : IsJordanCurve (frontier K) := by
  let L := Arcs.complexLIE
  have himage : L.symm.toHomeomorph '' closedBall (0 : Plane) 1 = closedBall (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_closedBall_zero_iff]
      change ‖L.symm w‖ ≤ 1
      rw [L.symm.norm_map]
      exact mem_closedBall_zero_iff.mp hw
    · intro hz
      refine ⟨L z, ?_, by simp⟩
      simpa only [mem_closedBall_zero_iff, L.norm_map] using hz
  let ep : closedBall (0 : Plane) 1 ≃ₜ K :=
    ((L.symm.toHomeomorph.image _).trans (Homeomorph.setCongr himage)).trans e
  have hfront : Subtype.val '' (ep '' {z | (z : Plane) ∈ sphere 0 1}) = frontier K := by
    ext x
    have hclosed : IsClosed K := (closure_interior_of_homeomorph_closedDisk e) ▸ isClosed_closure
    rw [hclosed.frontier_eq]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(ep z).2, ?_⟩
      have hz' : (L.symm z : ℂ) ∈ sphere 0 1 := by
        rw [mem_sphere_zero_iff_norm, L.symm.norm_map, ← mem_sphere_zero_iff_norm]
        exact hz
      intro hi
      let zc := ((L.symm.toHomeomorph.image _).trans (Homeomorph.setCongr himage)) z
      have hi' : (L.symm z : ℂ) ∈ interior (closedBall (0 : ℂ) 1) := by
        change (zc : ℂ) ∈ interior (closedBall (0 : ℂ) 1)
        apply (homeomorph_subspace_mem_interior_iff e zc).2
        change (e zc : ℂ) ∈ interior K at hi
        exact hi
      rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hi'
      have hlt := mem_ball_zero_iff.mp hi'
      rw [mem_sphere_zero_iff_norm.mp hz'] at hlt
      exact lt_irrefl _ hlt
    · rintro ⟨hx, hxi⟩
      let z := ep.symm ⟨x, hx⟩
      refine ⟨ep z, ⟨z, ?_, rfl⟩, by simp [z]⟩
      have hn : ¬ (z : Plane) ∈ ball 0 1 := by
        intro hz
        apply hxi
        apply interior_maximal (s := K) (t := Subtype.val '' (ep '' {z | (z : Plane) ∈ ball 0 1}))
          (by rintro _ ⟨y, _, rfl⟩; exact y.2) (isOpen_embedded_open_disk ep)
        exact ⟨ep z, ⟨z, hz, rfl⟩, by simp [z]⟩
      have hzle : dist (z : Plane) 0 ≤ 1 := z.2
      exact le_antisymm hzle (le_of_not_gt hn)
  rw [← hfront]
  exact isJordanCurve_embedded_disk_boundary ep

/-- If the interiors of two embedded disks are disjoint, their intersection is a
proper closed subset of both frontiers. -/
theorem embedded_disks_inter_frontiers {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B)) :
    IsClosed (A ∩ B) ∧ A ∩ B ⊆ frontier A ∧ A ∩ B ⊆ frontier B ∧
      (∃ p ∈ frontier A, p ∉ A ∩ B) ∧ (∃ p ∈ frontier B, p ∉ A ∩ B) := by
  have hA := closure_interior_of_homeomorph_closedDisk eA
  have hB := closure_interior_of_homeomorph_closedDisk eB
  have hAc : IsClosed A := hA ▸ isClosed_closure
  have hBc : IsClosed B := hB ▸ isClosed_closure
  have hinter := inter_eq_frontier_inter_frontier_of_regularClosed hA hB hdis
  have proper : ∀ {S T : Set ℂ} (eS : closedBall (0 : ℂ) 1 ≃ₜ S)
      (eT : closedBall (0 : ℂ) 1 ≃ₜ T),
      Disjoint (interior S) (interior T) → ∃ p ∈ frontier S, p ∉ S ∩ T := by
    intro S T eS eT hd
    have hSc : IsClosed S := (closure_interior_of_homeomorph_closedDisk eS) ▸ isClosed_closure
    have hScompact : IsCompact S := by
      have hr : range (fun x => (eS x : ℂ)) = S := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact (eS y).2
        · intro hx
          exact ⟨eS.symm ⟨x, hx⟩, by simp⟩
      rw [← hr]
      exact isCompact_range (continuous_subtype_val.comp eS.continuous)
    have hTpre := (complex_embedded_closed_disk_compl_preconnected_unbounded eT).1
    have hTunbounded := (complex_embedded_closed_disk_compl_preconnected_unbounded eT).2
    by_contra! hproper
    have hfront : frontier S ⊆ T := by
      intro x hx
      exact (hproper x hx).2
    have hcover : Tᶜ ⊆ interior S ∪ Sᶜ := by
      intro x hx
      by_cases hi : x ∈ interior S
      · exact Or.inl hi
      · right
        intro hs
        apply hx (hfront _)
        exact ⟨hSc.closure_eq.symm ▸ hs, hi⟩
    have hne : (Tᶜ ∩ Sᶜ).Nonempty := by
      by_contra hne
      have hsub : Tᶜ ⊆ S := by
        intro x hx
        by_contra hxs
        exact hne ⟨x, hx, hxs⟩
      exact hTunbounded (hScompact.isBounded.subset hsub)
    have hsub : Tᶜ ⊆ Sᶜ :=
      hTpre.subset_right_of_subset_union isOpen_interior hSc.isOpen_compl
        (disjoint_left.mpr (fun _ hi hc => hc (interior_subset hi))) hcover hne
    have hST : S ⊆ T := by
      intro x hx
      by_contra ht
      exact hsub ht hx
    obtain ⟨x, hx⟩ := (isConnected_interior_of_homeomorph_closedDisk eS).nonempty
    exact (disjoint_left.mp hd) hx (interior_mono hST hx)
  refine ⟨hAc.inter hBc, ?_, ?_, proper eA eB hdis, ?_⟩
  · rw [hinter]
    exact inter_subset_left
  · rw [hinter]
    exact inter_subset_right
  obtain ⟨p, hp, hp'⟩ := proper eB eA hdis.symm
  exact ⟨p, hp, fun h => hp' ⟨h.2, h.1⟩⟩

/-- A component of the intersection of two embedded disks with disjoint interiors
is a singleton or a Jordan arc. -/
theorem connectedComponentIn_embedded_disks_inter_eq_singleton_or_arc
    {A B : Set ℂ} (eA : closedBall (0 : ℂ) 1 ≃ₜ A)
    (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B)) {x : ℂ} (hx : x ∈ A ∩ B) :
    (∃ p : ℂ, connectedComponentIn (A ∩ B) x = {p}) ∨
      ∃ f : unitInterval → ℂ, Continuous f ∧ Function.Injective f ∧
        range f = connectedComponentIn (A ∩ B) x := by
  obtain ⟨hclosed, hsub, _, hproper, _⟩ := embedded_disks_inter_frontiers eA eB hdis
  exact connectedComponentIn_eq_singleton_or_arc_of_isJordanCurve
    (isJordanCurve_frontier_of_homeomorph_closedDisk eA) hclosed hsub hproper hx

end LatticeProb
