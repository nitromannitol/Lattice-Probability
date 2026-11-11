import LatticeProb.Analysis.RotationalAverage
import LatticeProb.Bonanno.LQGMetric.Field.WholePlaneLateral

/-!
# Rotation invariance of the radial point of the circle-average parametrisation

The radial point `radialPoint x = (|x|, 0)` of the parameter space `CircleParameter = (0, ∞) × ℂ` of circle
averages depends only on the modulus `‖x‖`, with the value `(1, 0)` at the origin. Rotations about the origin
preserve the modulus and fix the origin, so the radial point is invariant under them.

Circle averages follow Duplantier-Sheffield, arXiv:0808.1560, Section 3.1, p. 17 (the circle average `h_ε(z)`;
Proposition 3.2: the covariance is the mean value of `ξ` on a circle).
-/

namespace LatticeProb

/-- The radial point is invariant under rotations about the origin of the plane. -/
lemma radialPoint_rot (θ : ℝ) (x : ℂ) : radialPoint (RotationalAverage.rot θ x) = radialPoint x := by
  have hz : RotationalAverage.rot θ x = 0 ↔ x = 0 := by
    rw [← norm_eq_zero, RotationalAverage.norm_rot, norm_eq_zero]
  simp only [radialPoint, hz, RotationalAverage.norm_rot]

end LatticeProb
