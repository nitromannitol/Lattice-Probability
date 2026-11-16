import LatticeProb.Analysis.Schauder.Interior

/-!
# Adapters for the interior Schauder estimate

The interior Schauder estimate at unit scale with the body of
`LatticeProb.Analysis.Schauder.SchauderInterior` written out in full. The body is the one of the
Lattice-High-Contrast-Homogenization development (its `External/SchauderInterior` module). The
theorem is obtained from `LatticeProb.Analysis.Schauder.schauderInterior` by unfolding the
definition.
-/

namespace LatticeProb.Analysis.Schauder

/-- The interior Schauder estimate at unit scale, with the body of `SchauderInterior` written out
(Gilbarg and Trudinger, Theorem 4.6, at radius one). -/
theorem schauderInterior_expanded (d : ℕ) :
    ∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (K₀ K₁ : ℝ), ContDiff ℝ 2 u →
    (∀ x ∈ Metric.closedBall x₀ 2, |u x| ≤ K₀) →
    (∀ x ∈ Metric.closedBall x₀ 2, ∀ y ∈ Metric.closedBall x₀ 2,
      |∑ i, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]| ≤
          K₁ ∧
        |∑ i, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] -
            ∑ i, iteratedFDeriv ℝ 2 u y ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]| ≤
          K₁ * dist x y ^ α) →
    ∀ x ∈ Metric.closedBall x₀ 1, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K₀ + K₁) :=
  schauderInterior (d := d)

end LatticeProb.Analysis.Schauder
