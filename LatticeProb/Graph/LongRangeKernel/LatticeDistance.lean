import LatticeProb.Graph.LongRangeKernel.LatticeHeat
import LatticeProb.Graph.LongRangeKernel.LatticeVolume

/-!
# Gaussian upper bound in graph distance

The lattice distance identity from `LatticeVolume` converts the simple random walk
estimate to the upper Gaussian hypothesis with polynomial volume profile and exponent two.
-/

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The normalized lattice satisfies the upper Gaussian hypothesis with exponent two. -/
theorem weightedLattice_gaussian_upper (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).heat n x y ≤ ENNReal.ofReal
        (C / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (C * n)) ^ (1 / ((2 : ℝ) - 1))))) := by
  let A : ℝ := 3 ^ d * greenConst d
  let B : ℝ := 8 * (1 + 2 * d)
  let C : ℝ := A * 2 ^ d + B + 1
  have hA : 0 ≤ A := mul_nonneg (by positivity) (greenConst_nonneg d)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A * 2 ^ d ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by
    have hprod : 0 ≤ A * 2 ^ d := mul_nonneg hA (by positivity)
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro x y n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  let t : ℝ := (n : ℝ) ^ (1 / (2 : ℝ))
  have ht : 1 ≤ t := Real.one_le_rpow hnR (by norm_num)
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hv : 0 < (1 + t) ^ d := pow_pos (by linarith) d
  have hp : (1 + t) ^ d ≤ 2 ^ d * t ^ d := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t) (by linarith : 1 + t ≤ 2 * t) d
  have hpow : (n : ℝ) ^ (-(d : ℝ) / 2) = (t ^ d)⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((1 / (2 : ℝ)) * d) by ring,
      Real.rpow_neg hnpos.le, Real.rpow_mul hnpos.le, Real.rpow_natCast]
  have hpre : A * (n : ℝ) ^ (-(d : ℝ) / 2) ≤ C / (1 + t) ^ d := by
    rw [hpow, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (pow_pos htp d) hv).mpr
    calc
      A * (1 + t) ^ d ≤ A * (2 ^ d * t ^ d) := mul_le_mul_of_nonneg_left hp hA
      _ = (A * 2 ^ d) * t ^ d := by ring
      _ ≤ C * t ^ d := mul_le_mul_of_nonneg_right hAC (pow_nonneg htp.le d)
  have hexp : -((graphNorm (y - x) : ℝ) ^ 2) / (B * n) ≤
      -((graphNorm (y - x) : ℝ) ^ 2 / (C * n)) := by
    rw [neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_right hBC hnpos.le))
  rw [weightedLattice_heat_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (srwHeat_gaussian_linear_time hd hn (y - x)).trans
  change A * (n : ℝ) ^ (-(d : ℝ) / 2) *
    Real.exp (-((graphNorm (y - x) : ℝ) ^ 2) / (B * n)) ≤ _
  change _ ≤ C / (1 + t) ^ d *
    Real.exp (-((((lattice d).dist x y : ℝ) ^ (2 : ℝ) / (C * n)) ^
      (1 / ((2 : ℝ) - 1))))
  rw [lattice_dist_eq_graphNorm hd]
  norm_num only [Real.rpow_two, sub_self, sub_zero, one_div_one, Real.rpow_one]
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (div_nonneg hC.le hv.le)

end

end LatticeProb.Graph.LongRangeKernel
