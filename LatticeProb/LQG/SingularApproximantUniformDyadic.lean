import LatticeProb.LQG.SingularApproximantCoarseGeometric
import LatticeProb.LQG.SingularApproximantComparableScales

/-! # Uniform dyadic bounds for singular approximants -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- A common spatial circle bound and a dilated-mass bound control the mass
of a small dyadic ball uniformly over all dyadic regularization scales. -/
theorem exists_singular_approximant_uniform_dyadic_bound
    {γ α δ C r : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    (h : ℝ → ℂ → ℝ)
    (hh : ∀ k z, z ∈ ball (0 : ℂ) r →
      h (dyadicScale k) z ≤ C + (2 + δ) * Real.log (dyadicScale k)⁻¹)
    (hZ : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h)
            (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j))) :
    ∃ n : ℕ, 0 < n ∧ ∃ J₀ : ℕ, ∀ J k : ℕ,
      dyadicScale J ≤ r → J₀ ≤ J / n →
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
          Real.exp (-(Real.log 2) * J)))
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
            (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
              (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)))))) := by
  obtain ⟨n, hn, hcoarse⟩ := exists_singular_approximant_coarse_geometric hγ.le h hh
  obtain ⟨J₀, hcomparable⟩ :=
    LQGMeasureOriginBound.eventually_singular_approximant_ball_le_geometric_div hγ hαQ h hZ n
  refine ⟨n, hn, J₀, fun J k hr hJ => ?_⟩
  rcases le_total k (J / n) with hk | hk
  · exact (hcoarse J k hr hk).trans (le_max_left _ _)
  · exact (hcomparable J k hJ hk).trans (le_max_right _ _)

end LatticeProb.LQG
