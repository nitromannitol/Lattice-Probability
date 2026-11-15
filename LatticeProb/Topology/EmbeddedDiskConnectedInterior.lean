import LatticeProb.Topology.SubspaceHomeomorphInterior

/-! # Connected interior of an embedded disk -/

set_option autoImplicit false

open Set Metric Topology

namespace LatticeProb

/-- A planar set homeomorphic to the closed unit disk has connected interior. -/
theorem isConnected_interior_of_homeomorph_closedDisk {K : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ K) : IsConnected (interior K) := by
  let D : Set (closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ ball 0 1}
  have hDimage : Subtype.val '' D = ball (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      exact ⟨⟨z, ball_subset_closedBall hz⟩, hz, rfl⟩
  have hD : IsConnected D := by
    constructor
    · exact ⟨⟨0, by simp⟩, by simp [D]⟩
    · rw [← IsInducing.subtypeVal.isPreconnected_image, hDimage]
      exact isPreconnected_ball
  let f : closedBall (0 : ℂ) 1 → ℂ := fun z => e z
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have himage : f '' D = interior K := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply homeomorph_subspace_mem_interior e x
      change (x : ℂ) ∈ ball (0 : ℂ) 1 at hx
      simpa only [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] using hx
    · intro hz
      let x := e.symm ⟨z, interior_subset hz⟩
      have hx : (x : ℂ) ∈ interior (closedBall (0 : ℂ) 1) := by
        apply (homeomorph_subspace_mem_interior_iff e x).2
        simpa only [x, Homeomorph.apply_symm_apply] using hz
      refine ⟨x, ?_, ?_⟩
      · change (x : ℂ) ∈ ball (0 : ℂ) 1
        simpa only [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] using hx
      · simp only [f, x, Homeomorph.apply_symm_apply]
  rw [← himage]
  exact hD.image f hf.continuousOn

end LatticeProb
