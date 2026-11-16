import Mathlib

/-!
# The interior Schauder estimate at unit scale: statement

Gilbarg and Trudinger, *Elliptic partial differential equations of second order* (2001),
Theorem 4.6, at radius `R = 1`: if `u ∈ C²` and `Δu = f` with `f ∈ C^{0,α}` on the ball `B₂(x₀)`,
then `sup_{B₁(x₀)} |D²u| ≤ C(d,α) (sup_{B₂(x₀)} |u| + sup_{B₂(x₀)} |f| + [f]_{α;B₂(x₀)})`.

The statement is weaker than Theorem 4.6: `u` is `C²` on all of `ℝ^d`, only the sup of the second
derivatives is concluded, and the Hölder seminorm of `f` enters through the bound `K₁`. The
Laplacian is written out as `Σ_i ∂_i² u`.

The definition is ported from the Lattice-High-Contrast-Homogenization development (its
`External/SchauderInterior` module), without change of its body.
-/

/-- The interior Schauder estimate for Poisson's equation at unit scale (GT01, Theorem 4.6). -/
def LatticeProb.Analysis.Schauder.SchauderInterior (d : ℕ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (K₀ K₁ : ℝ), ContDiff ℝ 2 u →
    (∀ x ∈ Metric.closedBall x₀ 2, |u x| ≤ K₀) →
    (∀ x ∈ Metric.closedBall x₀ 2, ∀ y ∈ Metric.closedBall x₀ 2,
      |∑ i, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]| ≤
          K₁ ∧
        |∑ i, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] -
            ∑ i, iteratedFDeriv ℝ 2 u y ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]| ≤
          K₁ * dist x y ^ α) →
    ∀ x ∈ Metric.closedBall x₀ 1, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K₀ + K₁)
