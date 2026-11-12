import LatticeProb.Gauss.RegressionLimit

/-!
# The residual of the linear regression on a sequence of pairwise uncorrelated random variables

* `LatticeProb.Gauss.covariance_sq_le_variance_mul`: the Cauchy-Schwarz inequality
  `cov[X, W] ^ 2 ≤ Var[X] * Var[W]` for square integrable random variables.
* `LatticeProb.Gauss.tendsto_covariance_of_tendsto_L2`: the covariance with a fixed square integrable random variable
  is continuous for the convergence in `L²`.
* `LatticeProb.Gauss.covariance_sub_limit_regression_eq_zero`: if `ρ` is the `L²` limit of the partial linear
  regressions of `Y` on pairwise uncorrelated square integrable `η k`, the residual `Y - ρ` is uncorrelated with every
  `η l`.
* `LatticeProb.Gauss.tendsto_sum_covariance_limit_regression`: the covariance of the limit `ρ` with a square integrable
  `W` is the sum of the series `∑ k, (Var[η k])⁻¹ * cov[Y, η k] * cov[η k, W]`, as a limit of its partial sums.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Cauchy-Schwarz inequality for the covariance** of square integrable random variables. -/
theorem covariance_sq_le_variance_mul [IsFiniteMeasure P] {X W : Ω → ℝ} (hX : MemLp X 2 P)
    (hW : MemLp W 2 P) : cov[X, W; P] ^ 2 ≤ Var[X; P] * Var[W; P] := by
  by_cases h0 : Var[W; P] = 0
  · rw [covariance_eq_zero_of_variance_eq_zero_right X hW h0, h0]
    simp
  · have hpos : 0 < Var[W; P] := lt_of_le_of_ne (variance_nonneg W P) (Ne.symm h0)
    set t := cov[X, W; P] / Var[W; P] with ht
    have h := variance_nonneg (fun ω => X ω - t * W ω) P
    rw [variance_fun_sub hX (hW.const_mul t), covariance_const_mul_right, variance_const_mul] at h
    have htV : t * Var[W; P] = cov[X, W; P] := div_mul_cancel₀ _ h0
    have e : Var[W; P] * (Var[X; P] - 2 * (t * cov[X, W; P]) + t ^ 2 * Var[W; P]) =
        Var[W; P] * Var[X; P] - cov[X, W; P] ^ 2 := by
      calc Var[W; P] * (Var[X; P] - 2 * (t * cov[X, W; P]) + t ^ 2 * Var[W; P])
          = Var[W; P] * Var[X; P] - 2 * (t * Var[W; P]) * cov[X, W; P] + (t * Var[W; P]) ^ 2 := by ring
        _ = Var[W; P] * Var[X; P] - cov[X, W; P] ^ 2 := by rw [htV]; ring
    have hnn := mul_nonneg hpos.le h
    rw [e] at hnn
    nlinarith [hnn]

variable [IsProbabilityMeasure P]

/-- The covariance with a fixed square integrable random variable is continuous for the convergence in `L²`. -/
theorem tendsto_covariance_of_tendsto_L2 {X : ℕ → Ω → ℝ} {ξ W : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hξ : MemLp ξ 2 P) (hW : MemLp W 2 P)
    (h : Tendsto (fun n => ∫ ω, (X n ω - ξ ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => cov[X n, W; P]) atTop (𝓝 cov[ξ, W; P]) := by
  have hbound : ∀ n, |cov[X n, W; P] - cov[ξ, W; P]| ≤
      Real.sqrt ((∫ ω, (X n ω - ξ ω) ^ 2 ∂P) * Var[W; P]) := fun n => by
    rw [← covariance_sub_left (hX n) hξ hW, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    calc cov[X n - ξ, W; P] ^ 2 ≤ Var[X n - ξ; P] * Var[W; P] :=
          covariance_sq_le_variance_mul ((hX n).sub hξ) hW
      _ ≤ (∫ ω, (X n ω - ξ ω) ^ 2 ∂P) * Var[W; P] :=
          mul_le_mul_of_nonneg_right
            (variance_le_expectation_sq ((hX n).sub hξ).aestronglyMeasurable) (variance_nonneg _ _)
  have hlim : Tendsto (fun n => Real.sqrt ((∫ ω, (X n ω - ξ ω) ^ 2 ∂P) * Var[W; P])) atTop (𝓝 0) := by
    have h' := (h.mul_const (Var[W; P])).sqrt
    rwa [zero_mul, Real.sqrt_zero] at h'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hlim

/-- **The regression residual is uncorrelated with the regressors.** If `ρ` is the `L²` limit of the partial linear
regressions of `Y` on pairwise uncorrelated square integrable `η k`, then `Y - ρ` is uncorrelated with every `η l`. -/
theorem covariance_sub_limit_regression_eq_zero {Y ρ : Ω → ℝ} {η : ℕ → Ω → ℝ} (hY : MemLp Y 2 P)
    (hη : ∀ k, MemLp (η k) 2 P) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0) (hρ : MemLp ρ 2 P)
    (htend : Tendsto (fun n => ∫ ω, (partialRegression P Y η n ω - ρ ω) ^ 2 ∂P) atTop (𝓝 0)) (l : ℕ) :
    cov[fun ω => Y ω - ρ ω, η l; P] = 0 := by
  have h1 : Tendsto (fun n => cov[fun ω => Y ω - partialRegression P Y η n ω, η l; P]) atTop
      (𝓝 cov[fun ω => Y ω - ρ ω, η l; P]) := by
    refine tendsto_covariance_of_tendsto_L2 (X := fun n ω => Y ω - partialRegression P Y η n ω)
      (ξ := fun ω => Y ω - ρ ω) (fun n => hY.sub (memLp_partialRegression hη Y n)) (hY.sub hρ) (hη l) ?_
    refine htend.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have hzero : ∀ n ≥ l + 1, cov[fun ω => Y ω - partialRegression P Y η n ω, η l; P] = 0 := fun n hn =>
    covariance_sub_regression_eq_zero (s := Finset.range n) hY (fun k _ => hη k)
      (fun k _ l' _ h => horth k l' h) (Finset.mem_range.2 (by omega))
  have h2 : Tendsto (fun n => cov[fun ω => Y ω - partialRegression P Y η n ω, η l; P]) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨l + 1, fun n hn => (hzero n hn).symm⟩)
  exact tendsto_nhds_unique h1 h2

/-- The covariance of the `L²` limit `ρ` of the partial linear regressions of `Y` on square integrable `η k` with a
square integrable `W` is the limit of the partial sums of `∑ k, (Var[η k])⁻¹ * cov[Y, η k] * cov[η k, W]`. -/
theorem tendsto_sum_covariance_limit_regression {Y ρ W : Ω → ℝ} {η : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hρ : MemLp ρ 2 P) (hW : MemLp W 2 P)
    (htend : Tendsto (fun n => ∫ ω, (partialRegression P Y η n ω - ρ ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (Var[η k; P])⁻¹ * cov[Y, η k; P] * cov[η k, W; P]) atTop
      (𝓝 cov[ρ, W; P]) := by
  refine (tendsto_covariance_of_tendsto_L2 (memLp_partialRegression hη Y) hρ hW htend).congr fun n => ?_
  exact covariance_fun_sum_const_mul_left (fun k _ => hη k) hW fun k => (Var[η k; P])⁻¹ * cov[Y, η k; P]

end LatticeProb.Gauss
