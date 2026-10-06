/-
# Li--Shao normal comparison: the DCT inputs for route item 3

Continuing `LatticeProb/Prob/NormalComparisonFinalNine.lean`.  The raw orthant derivative
`d/dt ∫_{x ≤ b} covDensity S_t x dx` is obtained from the pointwise density derivative by
dominated convergence.  This file supplies its two analytic inputs and closes the pointwise
derivative:

* `integrable_one_add_sq_mul_exp_neg`: the Gaussian-polynomial majorant
  `(1 + ∑ xₖ²) exp (-(c ∑ xₖ²))` is integrable for `c > 0`;
* `abs_half_sum_sum_le`: the triangle inequality for the weighted double sum
  `|(1/2) ∑ᵢⱼ Bᵢⱼ Pᵢⱼ| ≤ ((1/2) ∑ᵢⱼ |Bᵢⱼ| C) w` when `|Pᵢⱼ| ≤ C w`;
* `hasDerivAt_covDensity_smartPath`: the pointwise density derivative along the smart path,
  now unconditional (it composes `normalComparisonSmartPath_eq_add_smul` with
  `hasDerivAt_covDensity_add_smul`).

No `External` is touched, no `Prop` is frozen, and nothing is claimed about `Rotor.External.LSS`.
-/
import LatticeProb.Prob.NormalComparisonFinalSeven
import LatticeProb.Prob.NormalComparisonFinalNine

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace LatticeProb

/-- The Gaussian `exp (-(c * ∑ xₖ²))` is integrable on `Fin n → ℝ` for `c > 0`: it is the product
`∏ₖ exp (-c xₖ²)` of one-dimensional Gaussians. -/
private lemma integrable_exp_neg_const_mul_sum_sq {n : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-(c * ∑ k, x k ^ 2))) := by
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ k, Real.exp (-c * x k ^ 2)) := by
    rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hc)
  refine hprod.congr (Filter.Eventually.of_forall fun x => ?_)
  show ∏ k, Real.exp (-c * x k ^ 2) = Real.exp (-(c * ∑ k, x k ^ 2))
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp only [neg_mul]

/-- **Gaussian-polynomial integrability.**  For `c > 0`, the function
`(1 + ∑ xₖ²) exp (-(c ∑ xₖ²))` is integrable on `Fin n → ℝ`. -/
theorem integrable_one_add_sq_mul_exp_neg {n : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin n → ℝ => (1 + ∑ k, x k ^ 2) * Real.exp (-(c * ∑ k, x k ^ 2))) := by
  have hI := (integrable_exp_neg_const_mul_sum_sq (n := n) (half_pos hc)).const_mul (1 + 2 / c)
  refine hI.mono' (by fun_prop : Continuous _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hq : 0 ≤ ∑ k, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  generalize ∑ k, x k ^ 2 = q at hq ⊢
  have h0 : c / 2 * q ≤ Real.exp (c / 2 * q) := by linarith [Real.add_one_le_exp (c / 2 * q)]
  have h1 : q ≤ 2 / c * Real.exp (c / 2 * q) := by
    calc q = 2 / c * (c / 2 * q) := by field_simp
      _ ≤ 2 / c * Real.exp (c / 2 * q) := mul_le_mul_of_nonneg_left h0 (by positivity)
  have h2 : 1 ≤ Real.exp (c / 2 * q) := Real.one_le_exp (by positivity)
  have h3 : 1 + q ≤ (1 + 2 / c) * Real.exp (c / 2 * q) := by nlinarith
  have h4 : Real.exp (c / 2 * q) * Real.exp (-(c * q)) = Real.exp (-(c / 2 * q)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + q) * Real.exp (-(c * q))
      ≤ ((1 + 2 / c) * Real.exp (c / 2 * q)) * Real.exp (-(c * q)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = (1 + 2 / c) * Real.exp (-(c / 2 * q)) := by rw [mul_assoc, h4]

/-- **Triangle inequality for the weighted double sum.**  If `|P i j| ≤ C * w` for all `i j`, then
`|(1/2) ∑ᵢⱼ Bᵢⱼ Pᵢⱼ| ≤ ((1/2) ∑ᵢⱼ |Bᵢⱼ| C) * w`. -/
theorem abs_half_sum_sum_le {n : ℕ} (B P : Fin n → Fin n → ℝ) {C w : ℝ}
    (hP : ∀ i j, |P i j| ≤ C * w) :
    |1 / 2 * ∑ i, ∑ j, B i j * P i j| ≤ (1 / 2 * ∑ i, ∑ j, |B i j| * C) * w := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |∑ i, ∑ j, B i j * P i j| ≤ ∑ i, |∑ j, B i j * P i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |B i j| * (C * w) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hP i j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |B i j| * C) * w := by simp only [Finset.sum_mul, mul_assoc]

/-- **Pointwise derivative of the density along the smart path, unconditional.**  For
`t ∈ [0, 1)`,
`d/dt covDensity S_t x
  = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ ((S_t⁻¹ x)ᵢ (S_t⁻¹ x)ⱼ - S_t⁻¹ᵢⱼ) covDensity S_t x`,
now that `hasDerivAt_covDensity_add_smul` is proved in `NormalComparisonFinalNine`. -/
theorem hasDerivAt_covDensity_smartPath {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => covDensity (normalComparisonSmartPath v S s) x)
      (1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t) x)) t :=
  hasDerivAt_covDensity_smartPath_of_add_smul hv hS ht
    (fun _ _ _ hPD x => hasDerivAt_covDensity_add_smul _ _ _ hPD x) x

end LatticeProb
