/-
# Normal comparison (Li--Shao): differentiating the orthant probability along the smart path

Route: `scratch/pk/normalcompare-route.md`, item 3.  For `v > 0`, `S` positive semidefinite and
`b : Fin n → ℝ`, the orthant probability along the smart path `S_t = (1 - t) • (v • 1) + t • S` is

  `F(t) = ∫_{x ≤ b} covDensity S_t x dx`,

and this file differentiates it under the integral sign for `t ∈ (0, 1)`:

  `F'(t) = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ ∫_{x ≤ b} ((S_t⁻¹ x)ᵢ (S_t⁻¹ x)ⱼ - (S_t⁻¹)ᵢⱼ) p_t(x) dx`,

with `p_t = covDensity S_t`.

* The smart path is the affine line `v • 1 + t • (S - v • 1)`
  (`normalComparisonSmartPath_eq_add_smul`), so the pointwise derivative of the density is
  `hasDerivAt_covDensity_add_smul` (`GaussCovDensityPath.lean`); it is positive definite for
  `t ∈ [0, 1)` (`normalComparisonSmartPath_posDef`).
* The Gaussian-polynomial weight `(1 + ∑ xₖ²) exp (-c ∑ xₖ²)` is integrable on `Fin n → ℝ`
  (`integrable_one_add_sq_mul_exp_neg`): it is dominated by a multiple of the product
  `∏ₖ exp (-(c/2) xₖ²)`, whose integrability is `Integrable.fintype_prod` applied to the
  one-dimensional Gaussian.
* The uniform majorants of `GaussCovDensityMajorant.lean` on `[0, T]`, `T < 1`, feed
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (derivative,
  `hasDerivAt_orthant_covDensity_path`) and `continuousOn_of_dominated` (continuity,
  `continuousOn_orthant_covDensity_path`) for the measure `volume.restrict (Set.Iic b)`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityPath
import LatticeProb.Prob.GaussCovDensityMajorant
import LatticeProb.Prob.GaussCovDensityIntegrable
import LatticeProb.Prob.NormalComparisonPath

open MeasureTheory Matrix Topology Filter

namespace LatticeProb

/-! ### The smart path as an affine line -/

/-- The smart path as an affine line of matrices:
`S_t = v • 1 + t • (S - v • 1)`. -/
theorem normalComparisonSmartPath_eq_add_smul {n : ℕ} (v : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) :
    normalComparisonSmartPath v S t =
      v • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  ext i j
  simp only [normalComparisonSmartPath, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  ring

/-! ### Gaussian-polynomial integrability on `Fin n → ℝ` -/

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

/-! ### Pointwise derivative and measurability along the smart path -/

/-- The density `covDensity S` is continuous in `x`, for every matrix `S`. -/
private lemma continuous_covDensity_path {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (covDensity S) := by
  unfold covDensity
  have h : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (S⁻¹ *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  fun_prop

/-- **Pointwise derivative of the density along the smart path**, for `t ∈ [0, 1)`:
`d/dt covDensity S_t x
  = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ ((S_t⁻¹ x)ᵢ (S_t⁻¹ x)ⱼ - S_t⁻¹ᵢⱼ) covDensity S_t x`. -/
theorem hasDerivAt_covDensity_smartPath {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (x : Fin n → ℝ) :
    HasDerivAt (fun s => covDensity (normalComparisonSmartPath v S s) x)
      (1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t) x)) t := by
  have hPD : (v • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (S - v • 1)).PosDef := by
    rw [← normalComparisonSmartPath_eq_add_smul]
    exact normalComparisonSmartPath_posDef hS hv ht
  have h := hasDerivAt_covDensity_add_smul (v • (1 : Matrix (Fin n) (Fin n) ℝ)) (S - v • 1) t
    hPD x
  simpa only [← normalComparisonSmartPath_eq_add_smul] using h

/-- Triangle inequality for the weighted double sum: if `|P i j| ≤ C * w` for all `i j`, then
`|(1/2) ∑ᵢⱼ Bᵢⱼ Pᵢⱼ| ≤ ((1/2) ∑ᵢⱼ |Bᵢⱼ| C) * w`. -/
private lemma abs_half_sum_sum_le {n : ℕ} (B P : Fin n → Fin n → ℝ) {C w : ℝ}
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

/-! ### Differentiating the orthant probability along the smart path -/

/-- **Route item 3.**  The derivative of the orthant probability along the smart path:
for `t₀ ∈ (0, 1)`,
`d/dt ∫_{x ≤ b} covDensity S_t x dx
  = (1/2) ∑ᵢⱼ (S - v • 1)ᵢⱼ ∫_{x ≤ b} ((S_t₀⁻¹ x)ᵢ (S_t₀⁻¹ x)ⱼ - S_t₀⁻¹ᵢⱼ) covDensity S_t₀ x dx`. -/
theorem hasDerivAt_orthant_covDensity_path {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (b : Fin n → ℝ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ∫ x in Set.Iic b,
          ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
              * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
              - (normalComparisonSmartPath v S t₀)⁻¹ i j)
            * covDensity (normalComparisonSmartPath v S t₀) x)) t₀ := by
  have hT : (t₀ + 1) / 2 ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  obtain ⟨C, c, hC, hc, hmaj⟩ := exists_partial2_path_majorant v hv S hS hT
  have hs : Set.Ioo (0 : ℝ) ((t₀ + 1) / 2) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds ht₀.1 (by linarith [ht₀.2])
  have hPD : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (normalComparisonSmartPath v S t).PosDef :=
    fun t ht => normalComparisonSmartPath_posDef hS hv ⟨ht.1.le, ht.2⟩
  have hPD₀ := hPD t₀ ht₀
  have hint : ∀ i j, Integrable (fun x : Fin n → ℝ =>
      (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t₀)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t₀) x))
      (volume.restrict (Set.Iic b)) := fun i j =>
    ((integrable_partial2_covDensity hPD₀ i j).const_mul _).restrict
  have hint' : Integrable (fun x : Fin n → ℝ =>
      1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t₀)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t₀) x))
      (volume.restrict (Set.Iic b)) :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Iic b))
    (F := fun t x => covDensity (normalComparisonSmartPath v S t) x)
    (F' := fun t x => 1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t) x))
    (bound := fun x => (1 / 2 * ∑ i, ∑ j, |(S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j| * C) *
      ((1 + ∑ k, x k ^ 2) * Real.exp (-(c * ∑ k, x k ^ 2))))
    hs (Filter.Eventually.of_forall fun t =>
      (continuous_covDensity_path _).aestronglyMeasurable)
    ((integrable_covDensity hPD₀).restrict) hint'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => by
      rw [Real.norm_eq_abs]
      exact abs_half_sum_sum_le _ _ fun i j =>
        (hmaj t ⟨ht.1.le, ht.2.le⟩ x i j).trans_eq (mul_assoc _ _ _))
    (((integrable_one_add_sq_mul_exp_neg hc).const_mul _).restrict)
    (Filter.Eventually.of_forall fun x t ht =>
      hasDerivAt_covDensity_smartPath hv hS ⟨ht.1.le, lt_of_lt_of_le ht.2 (by linarith [ht₀.2])⟩ x)
  refine key.2.congr_deriv ?_
  calc ∫ x in Set.Iic b, 1 / 2 * ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t₀)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t₀) x)
      = 1 / 2 * ∫ x in Set.Iic b, ∑ i, ∑ j, (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t₀)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t₀) x) := integral_const_mul _ _
    _ = 1 / 2 * ∑ i, ∑ j, ∫ x in Set.Iic b,
        (S - v • (1 : Matrix (Fin n) (Fin n) ℝ)) i j *
        ((((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) i
            * ((normalComparisonSmartPath v S t₀)⁻¹ *ᵥ x) j
            - (normalComparisonSmartPath v S t₀)⁻¹ i j)
          * covDensity (normalComparisonSmartPath v S t₀) x) := by
        congr 1
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ = _ := by simp only [integral_const_mul]

/-! ### Continuity of the orthant probability along the smart path -/

/-- **Continuity of the orthant probability** on `[0, T]`, `T < 1`:
`t ↦ ∫_{x ≤ b} covDensity S_t x dx` is continuous on `Set.Icc 0 T`. -/
theorem continuousOn_orthant_covDensity_path {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (b : Fin n → ℝ) {T : ℝ}
    (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    ContinuousOn (fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x)
      (Set.Icc 0 T) := by
  obtain ⟨C, c, hC, hc, hmaj⟩ := exists_covDensity_path_majorant v hv S hS hT
  have hPD : ∀ t ∈ Set.Icc (0 : ℝ) T, (normalComparisonSmartPath v S t).PosDef :=
    fun t ht => normalComparisonSmartPath_posDef hS hv ⟨ht.1, lt_of_le_of_lt ht.2 hT.2⟩
  refine continuousOn_of_dominated (μ := volume.restrict (Set.Iic b))
    (F := fun t x => covDensity (normalComparisonSmartPath v S t) x)
    (bound := fun x => C * Real.exp (-(c * ∑ k, x k ^ 2))) ?_ ?_ ?_ ?_
  · exact fun t _ => (continuous_covDensity_path _).aestronglyMeasurable
  · refine fun t ht => Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_pos (covDensity_pos (hPD t ht) x)]
    exact hmaj t ht x
  · exact ((integrable_exp_neg_const_mul_sum_sq hc).const_mul C).restrict
  · refine Filter.Eventually.of_forall fun x t ht => ?_
    exact (hasDerivAt_covDensity_smartPath hv hS ⟨ht.1, lt_of_le_of_lt ht.2 hT.2⟩ x).continuousAt
      |>.continuousWithinAt

end LatticeProb
