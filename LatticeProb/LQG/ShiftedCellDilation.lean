import LatticeProb.Topology.CompactCurveRange
import LatticeProb.LQG.ShiftedGridWalkAnchors

/-! # Scaling of shifted curve cells -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LatticeProb

/-- A time-rescaled curve has the same normalized cell path after rescaling the mesh. -/
theorem shiftedCellCurve_rescale_apply {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (η : C(ℝ, E)) (η' : C(ℝ, F)) (g : E → F) (b d θ : ℝ)
    (hη : ∀ t, η' t = g (η (b * t))) (k : ℤ) (u : unitInterval) :
    shiftedCellCurve η' d θ k u = g (shiftedCellCurve η (b * d) θ k u) := by
  simp only [shiftedCellCurve, movingIntervalCurve_apply, hη]
  congr 2; ring

/-- Scaling a shifted cell commutes with taking its compact range. -/
theorem shiftedCompactCell_rescale {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (η : C(ℝ, E)) (η' : C(ℝ, F)) (g : E → F) (b d θ : ℝ)
    (hη : ∀ t, η' t = g (η (b * t))) (k : ℤ) :
    (shiftedCompactCell η' d θ k : Set F) =
      g '' (shiftedCompactCell η (b * d) θ k : Set E) := by
  change range (shiftedCellCurve η' d θ k) = g '' range (shiftedCellCurve η (b * d) θ k)
  rw [← Set.range_comp]
  congr 1
  funext u
  exact shiftedCellCurve_rescale_apply η η' g b d θ hη k u

/-- The endpoint representative scales with the shifted cell. -/
theorem shiftedGridAnchor_rescale {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (η : C(ℝ, E)) (η' : C(ℝ, F)) (g : E → F) (b d θ : ℝ)
    (hη : ∀ t, η' t = g (η (b * t))) (k : ℤ) :
    shiftedGridAnchor η' d θ k = g (shiftedGridAnchor η (b * d) θ k) := by
  simp only [shiftedGridAnchor, hη, mul_assoc]

end LatticeProb
