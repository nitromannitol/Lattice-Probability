import LatticeProb.Gauss.RegressionGaussian

/-!
# Dual families for the linear regression on pairwise uncorrelated random variables

Let `η k`, `k ∈ ℕ`, be pairwise uncorrelated centred square integrable random variables and let `D k` be square
integrable random variables. With the weights `w k = (Var[η k])⁻¹` (zero when the variance vanishes), the *dual sum*
attached to coefficients `y : ℕ → ℝ` is `∑ k ∈ s, w k * y k * D k`. Evaluated at the regressors themselves,
`y = (η k ω')_k`, its second moment averaged over `ω'` is `∑ k ∈ s, w k * E[(D k)²]`: only the orthogonality of the
regressors is used, the dual family is arbitrary. This is the computation that makes the dual sums `L²`-Cauchy for
almost every value of the regressors when `∑ k, w k * E[(D k)²] < ∞`.

## Main results

* `LatticeProb.Gauss.exists_strictMono_forall_abs_le_of_tendsto`: one fast subsequence for countably many sequences
  tending to zero.
* `LatticeProb.Gauss.covariance_limit_regression_eq_zero`: the limit of the linear regressions is uncorrelated with
  every random variable uncorrelated with all regressors.
* `LatticeProb.Gauss.covariance_sub_limit_regression_of_covariance_eq_zero`: the residual of the limit regression has
  the same covariance as the regressed variable with such a random variable.
* `LatticeProb.Gauss.integral_integral_dualSum_sq`: the averaged second moment of the dual sums.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Common fast subsequence.** For countably many real sequences tending to zero there is one strictly increasing
sequence of indices `ns` such that `|a i (ns j)| ≤ 4⁻ʲ` whenever `i ≤ j`. -/
theorem exists_strictMono_forall_abs_le_of_tendsto {a : ℕ → ℕ → ℝ} (ha : ∀ i, Tendsto (a i) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ i j, i ≤ j → |a i (ns j)| ≤ (1 / 4 : ℝ) ^ j := by
  have hev : ∀ j, ∀ᶠ n in atTop, ∀ i, i ≤ j → |a i n| ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    have hj : ∀ i ∈ Finset.range (j + 1), ∀ᶠ n in atTop, |a i n| ≤ (1 / 4 : ℝ) ^ j := by
      intro i _
      filter_upwards [Metric.tendsto_nhds.1 (ha i) ((1 / 4 : ℝ) ^ j) (by positivity)] with n hn
      rw [Real.dist_eq, sub_zero] at hn
      exact hn.le
    filter_upwards [(eventually_all_finset _).2 hj] with n hn i hij
    exact hn i (Finset.mem_range.2 (Nat.lt_succ_of_le hij))
  obtain ⟨ns, hns, h⟩ := extraction_forall_of_eventually hev
  exact ⟨ns, hns, fun i j hij => h j i hij⟩

/-- The limit of the linear regressions of `Y` on `η` is uncorrelated with every square integrable random variable
that is uncorrelated with all regressors. -/
theorem covariance_limit_regression_eq_zero [IsProbabilityMeasure P] {Y ρ W : Ω → ℝ} {η : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hρ : MemLp ρ 2 P) (hW : MemLp W 2 P)
    (htend : Tendsto (fun n => ∫ ω, (partialRegression P Y η n ω - ρ ω) ^ 2 ∂P) atTop (𝓝 0))
    (hW0 : ∀ k, cov[η k, W; P] = 0) : cov[ρ, W; P] = 0 := by
  have h := tendsto_sum_covariance_limit_regression hη hρ hW htend
  simp only [hW0, mul_zero, Finset.sum_const_zero] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

/-- The residual of the limit regression of `Y` on `η` has the same covariance as `Y` with every square integrable
random variable that is uncorrelated with all regressors. -/
theorem covariance_sub_limit_regression_of_covariance_eq_zero [IsProbabilityMeasure P] {Y ρ W : Ω → ℝ}
    {η : ℕ → Ω → ℝ} (hY : MemLp Y 2 P) (hη : ∀ k, MemLp (η k) 2 P) (hρ : MemLp ρ 2 P) (hW : MemLp W 2 P)
    (htend : Tendsto (fun n => ∫ ω, (partialRegression P Y η n ω - ρ ω) ^ 2 ∂P) atTop (𝓝 0))
    (hW0 : ∀ k, cov[η k, W; P] = 0) : cov[fun ω => Y ω - ρ ω, W; P] = cov[Y, W; P] := by
  rw [covariance_fun_sub_left hY hρ hW, covariance_limit_regression_eq_zero hη hρ hW htend hW0, sub_zero]

/-- The dual sum `∑ k ∈ s, (Var[η k])⁻¹ * y k * D k ω` attached to the coefficients `y`. -/
noncomputable def dualSum (P : Measure Ω) (η D : ℕ → Ω → ℝ) (s : Finset ℕ) (y : ℕ → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ s, (Var[η k; P])⁻¹ * y k * D k ω

/-- The mixed second moments of pairwise uncorrelated centred square integrable random variables. -/
theorem integral_mul_eq_ite [IsProbabilityMeasure P] {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P)
    (hcen : ∀ k, P[η k] = 0) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0) (k l : ℕ) :
    ∫ ω, η k ω * η l ω ∂P = if k = l then Var[η k; P] else 0 := by
  have h := covariance_eq_sub (hη k) (hη l)
  rw [hcen k, hcen l, mul_zero, sub_zero] at h
  rw [show (∫ ω, η k ω * η l ω ∂P) = cov[η k, η l; P] from h.symm]
  split_ifs with hkl
  · rw [hkl, covariance_self (hη l).aemeasurable]
  · exact horth k l hkl

/-- **Averaged second moment of the dual sums.** For pairwise uncorrelated centred square integrable regressors `η`
and square integrable `D`,
`∫∫ (∑ k ∈ s, (Var[η k])⁻¹ * η k ω' * D k ω)² dP(ω) dP(ω') = ∑ k ∈ s, (Var[η k])⁻¹ * ∫ (D k)² dP`. -/
theorem integral_integral_dualSum_sq [IsProbabilityMeasure P] {η D : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hcen : ∀ k, P[η k] = 0) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0)
    (hD : ∀ k, MemLp (D k) 2 P) (s : Finset ℕ) :
    ∫ ω', ∫ ω, dualSum P η D s (fun k => η k ω') ω ^ 2 ∂P ∂P =
      ∑ k ∈ s, (Var[η k; P])⁻¹ * ∫ ω, D k ω ^ 2 ∂P := by
  have hinner : ∀ ω', ∫ ω, dualSum P η D s (fun k => η k ω') ω ^ 2 ∂P =
      ∑ k ∈ s, ∑ l ∈ s, ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * ∫ ω, D k ω * D l ω ∂P) *
        (η k ω' * η l ω') := by
    intro ω'
    have hsq : ∀ ω, dualSum P η D s (fun k => η k ω') ω ^ 2 =
        ∑ k ∈ s, ∑ l ∈ s, ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * (η k ω' * η l ω')) * (D k ω * D l ω) := by
      intro ω
      simp only [dualSum, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    have hint : ∀ k l, Integrable (fun ω => (Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * (η k ω' * η l ω') *
        (D k ω * D l ω)) P := fun k l => ((hD k).integrable_mul (hD l)).const_mul _
    simp_rw [hsq]
    rw [integral_finsetSum s fun k _ => integrable_finsetSum s fun l _ => hint k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum s fun l _ => hint k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    ring
  have hint : ∀ k l, Integrable (fun ω' => ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * ∫ ω, D k ω * D l ω ∂P) *
      (η k ω' * η l ω')) P := fun k l => ((hη k).integrable_mul (hη l)).const_mul _
  simp_rw [hinner]
  rw [integral_finsetSum s fun k _ => integrable_finsetSum s fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum s fun l _ => hint k l]
  simp_rw [integral_const_mul, integral_mul_eq_ite hη hcen horth, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq s k]
  simp only [hk, ↓reduceIte]
  by_cases hV : Var[η k; P] = 0
  · simp [hV]
  · simp only [sq]
    field_simp

end LatticeProb.Gauss
