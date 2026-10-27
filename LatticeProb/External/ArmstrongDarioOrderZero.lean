import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeBondCritical
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Order-zero approximation input

This module records the cited order-zero regularity and dimension statements for
supercritical bond clusters. The proposition is an explicit unproved assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb.Percolation

namespace LatticeProb.External

/-- Order-zero specialization of Armstrong–Dario, Theorem 2, for iid zero-one bonds. -/
def ArmstrongDarioOrderZero : Prop :=
  ∀ (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (p : unitInterval),
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ (s θ C : ℝ), 0 < s ∧ 0 < θ ∧ 0 < C ∧
      ∃ X : Configuration d → ℝ,
        Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧
        Integrable (fun ω => Real.exp (Real.rpow (X ω / θ) s)) (latticeBondLaw d p) ∧
        (∫ ω, Real.exp (Real.rpow (X ω / θ) s) ∂latticeBondLaw d p) ≤ 2 ∧
        ∀ᵐ ω ∂latticeBondLaw d p,
          ∃ _h : HasUniqueInfiniteOpenComponent ω,
            ∀ h' : HasUniqueInfiniteOpenComponent ω,
              FiniteDimensional ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) ∧
              Module.finrank ℝ (harmonicGrowthSpace (uniqueInfiniteComponent h') 0) = 1 ∧
              ∀ (R : ℝ), 2 * X ω ≤ R →
                ∀ u : uniqueInfiniteComponent h' → ℝ,
                  (∀ x ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R,
                    (∀ y : uniqueInfiniteComponent h',
                      (componentGraph (uniqueInfiniteComponent h')).Adj x y →
                        y ∈ componentEuclideanBall (uniqueInfiniteComponent h') 0 R) →
                    componentLaplacian (uniqueInfiniteComponent h') u x = 0) →
                  ∃ φ : uniqueInfiniteComponent h' → ℝ,
                    φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h') 0 ∧
                    ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
                      componentBallL2 (uniqueInfiniteComponent h') 0 r (u - φ) ≤
                        C * (r / R) * componentBallL2 (uniqueInfiniteComponent h') 0 R u

end LatticeProb.External
