/- Linearity of spatial directional differentiation.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.SpaceTimeDerivatives

noncomputable section
namespace LatticeProb.Scaling.SpaceTimeDerivatives
variable {d : ℕ}

/-- The spatial directional derivative in a fixed coordinate is linear: it distributes over
subtraction of two differentiable functions. -/
theorem spaceDeriv_sub {f g : ℝ × (Fin d → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin d) :
    spaceDeriv (fun p => f p - g p) i = fun p => spaceDeriv f i p - spaceDeriv g i p := by
  funext p
  simp only [spaceDeriv, fderiv_fun_sub (hf p) (hg p)]
  rfl

end LatticeProb.Scaling.SpaceTimeDerivatives
