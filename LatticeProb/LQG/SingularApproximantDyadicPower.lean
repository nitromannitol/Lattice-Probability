import LatticeProb.LQG.LQGMeasureOriginBound

/-! # Dyadic mass bound near a logarithmic singularity -/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG.LQGMeasureOriginBound

open LatticeProb.Gauss

/-- Subexponential growth of dilated masses yields a geometric bound for
regularization scales no larger than the ball radius. -/
theorem eventually_singular_approximant_ball_le_geometric {γ α : ℝ} (hγ : 0 < γ)
    (hαQ : α < lqgQ γ) (h : ℝ → ℂ → ℝ)
    (hZ : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j))) :
    ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ k ≥ J,
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
          (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ J /
            (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) := by
  have hσ : 0 < γ * (lqgQ γ - α) := mul_pos hγ (sub_pos.2 hαQ)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set σ := γ * (lqgQ γ - α) with hσdef
  set c := Real.exp (γ * (|α| * Real.log 2)) with hc
  set r := Real.exp (-(σ * Real.log 2 / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have : 0 < σ * Real.log 2 / 2 := by positivity
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hev := hZ (σ * Real.log 2 / 2) (by positivity)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hev
  refine ⟨J₀, ?_⟩
  intro J hJJ₀ k hk
  refine (lqgApprox_fieldCircleAverage_ball_dyadicScale_le_sum hγ α h hk).trans ?_
  have hterm : ∀ j ∈ Finset.Ico J (k + 1),
      ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (r ^ j) := by
    intro j hj
    have hjJ : J₀ ≤ j := hJJ₀.trans (Finset.mem_Ico.1 hj).1
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos' j).le _), mul_assoc]
    calc ENNReal.ofReal (dyadicScale j ^ σ) *
          (ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1))
        ≤ ENNReal.ofReal (dyadicScale j ^ σ) * ENNReal.ofReal (Real.exp (σ * Real.log 2 / 2 * j)) := by
          gcongr
          exact hJ₀ j hjJ
      _ = ENNReal.ofReal (r ^ j) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos' j).le _), hr,
            ← Real.exp_nat_mul, Real.rpow_def_of_pos (dyadicScale_pos' j), ← Real.exp_add]
          congr 2
          simp only [dyadicScale, Real.log_pow, Real.log_inv]
          ring
  calc ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)
      ≤ ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1), ENNReal.ofReal (r ^ j) := by
        gcongr with j hj
        exact hterm j hj
    _ = ENNReal.ofReal (c * ∑ j ∈ Finset.Ico J (k + 1), r ^ j) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg hr0 j)]
    _ ≤ ENNReal.ofReal (c * (r ^ J / (1 - r))) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (Real.exp_pos _).le)

end LatticeProb.LQG.LQGMeasureOriginBound
