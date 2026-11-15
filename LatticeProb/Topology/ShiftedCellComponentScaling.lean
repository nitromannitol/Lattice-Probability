import LatticeProb.LQG.ShiftedCellDilation
import LatticeProb.Topology.HomeomorphComponentCount

/-! # Component counts of rescaled shifted curve cells -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- Time rescaling and a spatial homeomorphism preserve the number of
non-singleton components in the intersection of two shifted curve cells. -/
theorem shifted_cell_inter_component_count_rescale
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (η : C(ℝ, E)) (η' : C(ℝ, F)) (h : E ≃ₜ F) (b d θ : ℝ)
    (hη : ∀ t, η' t = h (η (b * t))) (j k : ℤ) :
    {C ∈ connectedComponentIn
      ((shiftedCompactCell η' d θ j : Set F) ∩ (shiftedCompactCell η' d θ k : Set F)) ''
      ((shiftedCompactCell η' d θ j : Set F) ∩ (shiftedCompactCell η' d θ k : Set F)) |
        ¬ C.Subsingleton}.ncard =
    {C ∈ connectedComponentIn
      ((shiftedCompactCell η (b * d) θ j : Set E) ∩
        (shiftedCompactCell η (b * d) θ k : Set E)) ''
      ((shiftedCompactCell η (b * d) θ j : Set E) ∩
        (shiftedCompactCell η (b * d) θ k : Set E)) | ¬ C.Subsingleton}.ncard := by
  rw [shiftedCompactCell_rescale η η' h b d θ hη j,
      shiftedCompactCell_rescale η η' h b d θ hη k]
  exact ncard_nonsubsingleton_inter_components_image h _ _

end LatticeProb
