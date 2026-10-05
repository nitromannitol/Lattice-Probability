/-
# Li--Shao normal comparison: the interpolation on `[0, T]` (route item 8)

Assembly of the Li--Shao normal comparison along the smart path
`normalComparisonSmartPath v S t = (1 - t) • (v • 1) + t • S` for a positive semidefinite `S`
with constant diagonal `v > 0` and nonnegative entries.  Write
`F t = ∫_{x ≤ b} covDensity S_t x dx` for the orthant probability.  On `[0, T]`, `T < 1`:

* `F` is continuous (`continuousOn_orthant_covDensity_path`), with derivative
  `∑ᵢ ∑_{j > i} Sᵢⱼ I_ij(S_t)` on `(0, 1)` (`hasDerivAt_orthant_covDensity_path_pairs`);
* the mixed-partial orthant integrals satisfy `0 ≤ I_ij(S_t) ≤ p_v(t Sᵢⱼ / v; bᵢ, bⱼ)`
  (`orthantPartial2_nonneg_le`), so the derivative is nonnegative and at most
  `∑ᵢ ∑_{j > i} Sᵢⱼ p_v(t Sᵢⱼ / v; bᵢ, bⱼ)`;
* the mean value theorem gives monotonicity of `F` on `[0, T]`, and the integrated derivative
  bound `sub_le_integral_of_hasDeriv_right_of_le` together with
  `integral_bivariateGaussDensity_Icc_le` gives
  `F T - F 0 ≤ ∑ᵢ ∑_{j > i} Sᵢⱼ (4 v)⁻¹ exp (-(bᵢ² + bⱼ²) / (2 v (1 + T Sᵢⱼ / v)))`.

## Main results

* `orthant_path_interpolation`: both statements above.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityOrthantPath
import LatticeProb.Prob.GaussCovDensityOrthantPairs
import LatticeProb.Prob.GaussCovDensityPartial2Bounds
import LatticeProb.Prob.GaussCovDensityBoundary
import LatticeProb.Prob.NormalComparisonOrthantIcc

open MeasureTheory Matrix

namespace LatticeProb

/-- A positive semidefinite real matrix with constant diagonal `v > 0` has all entries at most
`v` (the case `i = j` is `hdiag`; otherwise `|S i j| ≤ v` by `abs_apply_le_of_posSemidef_diag`
once the dimension is written as `m + 2`). -/
private theorem apply_le_of_posSemidef_diag {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (i j : Fin n) : S i j ≤ v := by
  by_cases hij : i = j
  · subst hij
    exact (hdiag i).le
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
      refine ⟨n - 2, ?_⟩
      by_contra hn
      apply hij
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    exact (le_abs_self _).trans (abs_apply_le_of_posSemidef_diag hv hS hdiag i j)

/-- **Route item 8, interpolation on `[0, T]`.**  For `S` positive semidefinite with constant
diagonal `v > 0` and nonnegative entries, and `T ∈ [0, 1)`, the orthant probability
`∫_{x ≤ b} covDensity S_t x dx` is nondecreasing from `t = 0` to `t = T`, and its increase is at
most `∑ᵢ ∑_{j > i} Sᵢⱼ (4 v)⁻¹ exp (-(bᵢ² + bⱼ²) / (2 v (1 + T Sᵢⱼ / v)))`. -/
theorem orthant_path_interpolation {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (hnonneg : ∀ i j, 0 ≤ S i j) (b : Fin n → ℝ) {T : ℝ} (hT : T ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S 0) x)
        ≤ ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S T) x ∧
      (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S T) x)
        - (∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S 0) x)
      ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
          ((4 * v)⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * v * (1 + T * (S i j / v))))) := by
  have hr : ∀ i j, 0 ≤ S i j / v ∧ S i j / v ≤ 1 := fun i j =>
    ⟨div_nonneg (hnonneg i j) hv.le,
      (div_le_one hv).mpr (apply_le_of_posSemidef_diag hv hS hdiag i j)⟩
  have hRHS : 0 ≤ ∑ i, ∑ j ∈ Finset.Ioi i, S i j *
      ((4 * v)⁻¹ * Real.exp (-(b i ^ 2 + b j ^ 2) / (2 * v * (1 + T * (S i j / v))))) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hnonneg i j) (mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.exp_nonneg _))
  rcases hT.1.eq_or_lt with h0 | hpos
  · subst h0
    exact ⟨le_refl _, by rw [sub_self]; exact hRHS⟩
  · set F : ℝ → ℝ := fun t => ∫ x in Set.Iic b, covDensity (normalComparisonSmartPath v S t) x
      with hF
    set f' : ℝ → ℝ := fun t => ∑ i, ∑ j ∈ Finset.Ioi i,
      S i j * orthantPartial2 (normalComparisonSmartPath v S t) b i j with hf'
    set φ : ℝ → ℝ := fun t => ∑ i, ∑ j ∈ Finset.Ioi i,
      S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j) with hφ
    have hico : ∀ t ∈ Set.Ioo (0 : ℝ) T, t ∈ Set.Ico (0 : ℝ) 1 := fun t ht =>
      ⟨ht.1.le, ht.2.trans hT.2⟩
    have hcont : ContinuousOn F (Set.Icc 0 T) := continuousOn_orthant_covDensity_path hv hS b hT
    have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt F (f' t) t := fun t ht =>
      hasDerivAt_orthant_covDensity_path_pairs hv hS hdiag b ⟨ht.1, ht.2.trans hT.2⟩
    have hnn : ∀ t ∈ Set.Ioo (0 : ℝ) T, 0 ≤ f' t := fun t ht =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj =>
        mul_nonneg (hnonneg i j)
          (orthantPartial2_nonneg_le hv hS hdiag (hico t ht) b (Finset.mem_Ioi.mp hj).ne).1
    have hle : ∀ t ∈ Set.Ioo (0 : ℝ) T, f' t ≤ φ t := fun t ht =>
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => by
        have h := (orthantPartial2_nonneg_le hv hS hdiag (hico t ht) b
          (Finset.mem_Ioi.mp hj).ne).2
        rw [mul_div_assoc] at h
        exact mul_le_mul_of_nonneg_left h (hnonneg i j)
    have hterm : ∀ i j, ContinuousOn
        (fun t : ℝ => S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j))
        (Set.Icc 0 T) := fun i j =>
      continuousOn_const.mul
        (continuousOn_bivariateGaussDensity_path hv (hr i j).1 (hr i j).2 hT.2)
    have hsum : ∀ i, ContinuousOn
        (fun t : ℝ => ∑ j ∈ Finset.Ioi i,
          S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j)) (Set.Icc 0 T) :=
      fun i => continuousOn_finsetSum _ fun j _ => hterm i j
    have hφcont : ContinuousOn φ (Set.Icc 0 T) :=
      continuousOn_finsetSum _ fun i _ => hsum i
    have hmono : MonotoneOn F (Set.Icc 0 T) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hcont ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hderiv t ht).deriv]
        exact hnn t ht
    have h1 : F T - F 0 ≤ ∫ t in (0 : ℝ)..T, φ t :=
      intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hpos.le hcont
        (fun t ht => (hderiv t ht).hasDerivWithinAt) hφcont.integrableOn_Icc hle
    refine ⟨hmono (Set.left_mem_Icc.mpr hpos.le) (Set.right_mem_Icc.mpr hpos.le) hpos.le,
      h1.trans ?_⟩
    have hint1 : ∀ i, IntervalIntegrable
        (fun t : ℝ => ∑ j ∈ Finset.Ioi i,
          S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j)) volume 0 T :=
      fun i => ContinuousOn.intervalIntegrable_of_Icc hpos.le (hsum i)
    have hint2 : ∀ i j, IntervalIntegrable
        (fun t : ℝ => S i j * bivariateGaussDensity v (t * (S i j / v)) (b i) (b j))
        volume 0 T :=
      fun i j => ContinuousOn.intervalIntegrable_of_Icc hpos.le (hterm i j)
    simp only [hφ]
    rw [intervalIntegral.integral_finsetSum fun i _ => hint1 i]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => hint2 i j]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_bivariateGaussDensity_Icc_le hv (hr i j).1 (hr i j).2 hT.1 hT.2) (hnonneg i j)

end LatticeProb
