import LatticeProb.LQG.SingularApproximantCoarseExponent

/-! # Geometric bounds below the regularization scale -/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- A common spatial circle bound implies geometric decay of the mass at
coarse regularization scales. The scale ratio depends only on the parameters. -/
theorem exists_singular_approximant_coarse_geometric
    {γ α δ C r : ℝ} (hγ : 0 ≤ γ) (h : ℝ → ℂ → ℝ)
    (hh : ∀ k z, z ∈ ball (0 : ℂ) r →
      h (dyadicScale k) z ≤ C + (2 + δ) * Real.log (dyadicScale k)⁻¹) :
    ∃ n : ℕ, 0 < n ∧ ∀ J k : ℕ, dyadicScale J ≤ r → k ≤ J / n →
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
          Real.exp (-(Real.log 2) * J)) := by
  let b : ℝ := γ * (2 + δ) + γ * α - γ ^ 2 / 2
  obtain ⟨n, hn⟩ := exists_nat_gt (max b 0)
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right b 0) hn
    exact_mod_cast this
  refine ⟨n, hnpos, fun J k hJ hk => ?_⟩
  have hkJ : k ≤ J := hk.trans (Nat.div_le_self J n)
  have hnk : n * k ≤ J := by
    have h := (Nat.le_div_iff_mul_le hnpos).mp hk
    simpa [Nat.mul_comm] using h
  have hb : b ≤ (n : ℝ) := (le_max_left b 0).trans hn.le
  have hbJ : b * (k : ℝ) ≤ J := by
    have hmul : b * (k : ℝ) ≤ (n : ℝ) * k :=
      mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k)
    have hcast : (n : ℝ) * k ≤ J := by exact_mod_cast hnk
    exact hmul.trans hcast
  have hbase := lqgApprox_singular_dyadic_ball_le_exp (α := α) (δ := δ)
    (C := C) hγ h hkJ (fun z hz => hh k z (ball_subset_ball hJ hz))
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  change Real.log 2 * (b * (k : ℝ) - 2 * J) ≤ -(Real.log 2) * J
  nlinarith

end LatticeProb.LQG
