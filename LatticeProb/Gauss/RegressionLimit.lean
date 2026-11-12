import LatticeProb.Gauss.CameronMartinLimitShift
import LatticeProb.Prob.CovarianceRegression

/-!
# Limits of linear regressions on a sequence of pairwise uncorrelated random variables

Let `η k`, `k ∈ ℕ`, be pairwise uncorrelated, centred, square integrable real random variables and `Y` a square
integrable random variable. The partial linear regressions
`∑ k < n, (Var[η k])⁻¹ * cov[Y, η k] * η k` of `Y` on `η 0, …, η (n - 1)` form a Cauchy sequence in `L²`: the
second moment of the difference of two of them is a block of the series of Bessel's inequality. Hence they converge
in `L²` to a square integrable random variable, the linear regression of `Y` on the whole sequence, and a subsequence
converges almost surely.

* `LatticeProb.Gauss.exists_tendsto_L2_of_cauchy_L2`: Riesz-Fischer, with the `L²` convergence of the whole sequence
  and the almost sure convergence of a subsequence.
* `LatticeProb.Gauss.partialRegression`: the partial linear regressions.
* `LatticeProb.Gauss.integral_sq_partialRegression_sub`: the second moment of the difference of two partial
  regressions.
* `LatticeProb.Gauss.exists_tendsto_partialRegression`: the partial regressions converge in `L²` to a measurable square
  integrable limit, and almost surely along a subsequence.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Riesz-Fischer.** A sequence of square integrable functions which is Cauchy in `L²` converges in `L²` to a
measurable square integrable function, and a subsequence converges to it almost everywhere. -/
theorem exists_tendsto_L2_of_cauchy_L2 {X : ℕ → Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hcauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (X n ω - X k ω) ^ 2 ∂P < ε) :
    ∃ (ξ : Ω → ℝ) (ns : ℕ → ℕ), Measurable ξ ∧ MemLp ξ 2 P ∧
      Tendsto (fun n => ∫ ω, (X n ω - ξ ω) ^ 2 ∂P) atTop (𝓝 0) ∧ StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => X (ns i) ω) atTop (𝓝 (ξ ω)) := by
  set F : ℕ → Lp ℝ 2 P := fun n => (hX n).toLp (X n) with hF
  have hcs : CauchySeq F := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hcauchy (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn k hk => ?_⟩
    have hsq : ‖F n - F k‖ ^ 2 = ∫ ω, (X n ω - X k ω) ^ 2 ∂P := by
      rw [hF]
      simp only
      rw [← MemLp.toLp_sub (hX n) (hX k), norm_toLp_two_sq]
      rfl
    rw [dist_eq_norm]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [hsq]
    exact hN n hn k hk
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hGm : MemLp (G : Ω → ℝ) 2 P := Lp.memLp G
  refine ⟨G, ns, (Lp.stronglyMeasurable G).measurable, hGm, ?_, hns, ?_⟩
  · have hnorm : ∀ n, ‖F n - G‖ ^ 2 = ∫ ω, (X n ω - G ω) ^ 2 ∂P := fun n => by
      have hG' : hGm.toLp (G : Ω → ℝ) = G := Lp.toLp_coeFn G hGm
      rw [hF]
      simp only
      conv_lhs => rw [← hG']
      rw [← MemLp.toLp_sub (hX n) hGm, norm_toLp_two_sq]
      rfl
    have h0 := (tendsto_iff_norm_sub_tendsto_zero.1 hG).pow 2
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at h0
    exact h0.congr hnorm
  · have hrep : ∀ᵐ ω ∂P, ∀ n, F n ω = X n ω := ae_all_iff.2 fun n => (hX n).coeFn_toLp
    filter_upwards [hae, hrep] with ω hω hr
    exact hω.congr fun i => hr (ns i)

/-- The partial linear regression `∑ k < n, (Var[η k])⁻¹ * cov[Y, η k] * η k` of `Y` on the first `n` terms of a
sequence `η` of random variables. -/
noncomputable def partialRegression (P : Measure Ω) (Y : Ω → ℝ) (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω

/-- The partial regressions of a random variable on square integrable random variables are square integrable. -/
theorem memLp_partialRegression {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P) (Y : Ω → ℝ) (n : ℕ) :
    MemLp (partialRegression P Y η n) 2 P :=
  memLp_finsetSum (Finset.range n) fun k _ => (hη k).const_mul _

variable [IsProbabilityMeasure P]

/-- For pairwise uncorrelated centred square integrable `η k`, the second moment of the difference of the partial
regressions of `Y` on the first `n` and the first `m ≤ n` terms is the block `m ≤ k < n` of the series of Bessel's
inequality. -/
theorem integral_sq_partialRegression_sub (Y : Ω → ℝ) {η : ℕ → Ω → ℝ} (hη : ∀ k, MemLp (η k) 2 P)
    (hcen : ∀ k, P[η k] = 0) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0) {m n : ℕ} (hmn : m ≤ n) :
    ∫ ω, (partialRegression P Y η n ω - partialRegression P Y η m ω) ^ 2 ∂P =
      ∑ k ∈ Finset.Ico m n, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 := by
  set a : ℕ → ℝ := fun k => (Var[η k; P])⁻¹ * cov[Y, η k; P] with ha
  have hL2 : MemLp (fun ω => ∑ k ∈ Finset.Ico m n, a k * η k ω) 2 P :=
    memLp_finsetSum (Finset.Ico m n) fun k _ => (hη k).const_mul _
  have hmean : P[fun ω => ∑ k ∈ Finset.Ico m n, a k * η k ω] = 0 := by
    rw [integral_finsetSum _ fun k _ => ((hη k).const_mul (a k)).integrable one_le_two]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, hcen k, mul_zero]
  calc ∫ ω, (partialRegression P Y η n ω - partialRegression P Y η m ω) ^ 2 ∂P
      = ∫ ω, (∑ k ∈ Finset.Ico m n, a k * η k ω) ^ 2 ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [partialRegression, ha]
        rw [Finset.sum_Ico_eq_sub _ hmn]
    _ = Var[fun ω => ∑ k ∈ Finset.Ico m n, a k * η k ω; P] :=
        (variance_of_integral_eq_zero hL2.aemeasurable hmean).symm
    _ = ∑ k ∈ Finset.Ico m n, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 :=
        variance_regression Y (fun k _ => hη k) fun k _ l _ h => horth k l h

/-- **Linear regression on a sequence of pairwise uncorrelated random variables.** For pairwise uncorrelated centred
square integrable `η k` and square integrable `Y`, the partial regressions of `Y` on `η 0, …, η (n - 1)` converge in
`L²` to a measurable square integrable random variable `ρ`, and almost surely along a subsequence. -/
theorem exists_tendsto_partialRegression {Y : Ω → ℝ} {η : ℕ → Ω → ℝ} (hY : MemLp Y 2 P)
    (hη : ∀ k, MemLp (η k) 2 P) (hcen : ∀ k, P[η k] = 0) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0) :
    ∃ (ρ : Ω → ℝ) (ns : ℕ → ℕ), Measurable ρ ∧ MemLp ρ 2 P ∧
      Tendsto (fun n => ∫ ω, (partialRegression P Y η n ω - ρ ω) ^ 2 ∂P) atTop (𝓝 0) ∧ StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => partialRegression P Y η (ns i) ω) atTop (𝓝 (ρ ω)) := by
  set c : ℕ → ℝ := fun k => (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 with hc
  have hsum : Summable c := summable_inv_variance_mul_covariance_sq hY hη horth
  have hS : CauchySeq fun n => ∑ k ∈ Finset.range n, c k := hsum.hasSum.tendsto_sum_nat.cauchySeq
  refine exists_tendsto_L2_of_cauchy_L2 (memLp_partialRegression hη Y) fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hS ε hε
  refine ⟨N, fun n hn k hk => ?_⟩
  have hblock : ∀ {i j : ℕ}, i ≥ N → j ≥ N → i ≤ j →
      ∫ ω, (partialRegression P Y η j ω - partialRegression P Y η i ω) ^ 2 ∂P < ε := by
    intro i j hi hj hij
    rw [integral_sq_partialRegression_sub Y hη hcen horth hij, Finset.sum_Ico_eq_sub _ hij]
    have h := hN j hj i hi
    rw [Real.dist_eq] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  rcases le_total k n with hkn | hnk
  · exact hblock hk hn hkn
  · have h := hblock hn hk hnk
    have hsymm : ∀ ω, (partialRegression P Y η n ω - partialRegression P Y η k ω) ^ 2 =
        (partialRegression P Y η k ω - partialRegression P Y η n ω) ^ 2 := fun ω => by ring
    simpa only [hsymm] using h

end LatticeProb.Gauss
