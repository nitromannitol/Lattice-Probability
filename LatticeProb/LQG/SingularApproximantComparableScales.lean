import LatticeProb.LQG.SingularApproximantDyadicPower

/-! # Singular approximation bounds at comparable dyadic scales -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG.LQGMeasureOriginBound

open LatticeProb.Gauss

/-- The geometric estimate extends to balls whose dyadic index is at most a fixed
multiple of the regularization index. -/
theorem eventually_singular_approximant_ball_le_geometric_div
    {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ) (h : ℝ → ℂ → ℝ)
    (hZ : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j))) (n : ℕ) :
    ∃ J₀ : ℕ, ∀ J k : ℕ, J₀ ≤ J / n → J / n ≤ k →
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
          (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
            (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_singular_approximant_ball_le_geometric hγ hαQ h hZ
  refine ⟨J₀, fun J k hJ hk => ?_⟩
  have hscale : dyadicScale J ≤ dyadicScale (J / n) := by
    unfold dyadicScale
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_self J n)
  exact (measure_mono (ball_subset_ball hscale)).trans (hJ₀ (J / n) hJ k hk)

end LatticeProb.LQG.LQGMeasureOriginBound
