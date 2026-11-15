import LatticeProb.Topology.EmbeddedDiskOpen

/-! The boundary and interior of an embedded disk. -/

set_option autoImplicit false

noncomputable section

open Set Metric
open LQGMetric.JordanMap
open MatedCRTHarmonic.Planar.Jordan

namespace LatticeProb

/-- The boundary of an embedded closed disk is a Jordan curve. -/
theorem isJordanCurve_embedded_disk_boundary {K : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K) :
    IsJordanCurve (Subtype.val '' (e '' {z | (z : Plane) ∈ sphere 0 1})) := by
  let L := Arcs.complexLIE
  let s : sphere (0 : ℂ) 1 → closedBall (0 : Plane) 1 := fun z =>
    ⟨L z, by
      rw [mem_closedBall_zero_iff, L.norm_map]
      exact le_of_eq (mem_sphere_zero_iff_norm.mp z.2)⟩
  let f : sphere (0 : ℂ) 1 → ℂ := fun z => e (s z)
  let F : ℂ → ℂ := Function.extend Subtype.val f (fun _ => 0)
  have hF : ∀ z : sphere (0 : ℂ) 1, F z = f z := fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z
  have hs : Continuous s := by
    apply Continuous.subtype_mk
    exact L.continuous.comp continuous_subtype_val
  have hf : Continuous f := continuous_subtype_val.comp (e.continuous.comp hs)
  have hi : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    apply L.injective
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact hf.congr (fun z => (hF z).symm)
  · intro z hz w hw h
    exact congrArg Subtype.val (hi ((hF ⟨z, hz⟩).symm.trans (h.trans (hF ⟨w, hw⟩))))
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e (s ⟨z, hz⟩), ⟨s ⟨z, hz⟩, ?_, rfl⟩, ?_⟩
      · change L z ∈ sphere (0 : Plane) 1
        rw [mem_sphere_zero_iff_norm, L.norm_map]
        exact mem_sphere_zero_iff_norm.mp hz
      · exact (hF ⟨z, hz⟩).symm
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hp' : L.symm p ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, L.symm.norm_map, ← mem_sphere_zero_iff_norm]
        exact hp
      refine ⟨L.symm p, hp', ?_⟩
      rw [show F (L.symm p) = f ⟨L.symm p, hp'⟩ from hF ⟨L.symm p, hp'⟩]
      change (e (s ⟨L.symm p, hp'⟩) : ℂ) = (e p : ℂ)
      have heq : s ⟨L.symm p, hp'⟩ = p := Subtype.ext (L.apply_symm_apply p)
      rw [heq]

/-- The image of the open disk under an embedding of the closed disk is open. -/
theorem isOpen_embedded_open_disk {K : Set ℂ}
    (e : closedBall (0 : Plane) 1 ≃ₜ K) :
    IsOpen (Subtype.val '' (e '' {z | (z : Plane) ∈ ball 0 1})) :=
  isOpen_embedded_disk_open_image e (isJordanCurve_embedded_disk_boundary e) rfl

end LatticeProb
