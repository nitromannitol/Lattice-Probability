import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Energy estimate for compositions with adjoints -/

set_option autoImplicit false

namespace LatticeProb

/-- Differences in the domain of an adjoint composition satisfy the energy
estimate needed to control the intermediate image. -/
theorem norm_sub_apply_sq_le_adjoint_composition {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (G : E →ₗ.[ℂ] F) (hdense : Dense (G.domain : Set E))
    (u v : G.domain) (hu : G u ∈ G.adjoint.domain) (hv : G v ∈ G.adjoint.domain) :
    ‖G u - G v‖ ^ 2 ≤ ‖(u : E) - (v : E)‖ *
      ‖G.adjoint ⟨G u, hu⟩ - G.adjoint ⟨G v, hv⟩‖ := by
  let w : G.domain := u - v
  have hw : G w ∈ G.adjoint.domain := by
    simpa only [w, LinearPMap.map_sub] using G.adjoint.domain.sub_mem hu hv
  have henergy := (LinearPMap.adjoint_isFormalAdjoint hdense).symm w ⟨G w, hw⟩
  have hbound := norm_inner_le_norm (𝕜 := ℂ) (w : E) (G.adjoint ⟨G w, hw⟩)
  rw [← henergy, inner_self_eq_norm_sq_to_K] at hbound
  have heq : G.adjoint ⟨G w, hw⟩ =
      G.adjoint ⟨G u, hu⟩ - G.adjoint ⟨G v, hv⟩ := by
    have hs : (⟨G w, hw⟩ : G.adjoint.domain) = ⟨G u, hu⟩ - ⟨G v, hv⟩ := by
      apply Subtype.ext
      simp only [w, LinearPMap.map_sub, Submodule.coe_sub]
    rw [hs, LinearPMap.map_sub]
  rw [heq] at hbound
  simpa only [norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    w, LinearPMap.map_sub, Submodule.coe_sub] using hbound

end LatticeProb
