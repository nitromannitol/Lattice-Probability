import LatticeProb.Gauss.RegressionDual

/-!
# Dual sums along a fast subsequence are almost surely Cauchy in `L²`

Continuation of `LatticeProb.Gauss.RegressionDual`. Let `η k`, `k ∈ ℕ`, be pairwise uncorrelated centred square
integrable random variables with weights `w k = (Var[η k])⁻¹` (zero when the variance vanishes) and let `D k` be square
integrable random variables. The dual sum `∑ k ∈ s, w k * y k * D k` has covariance `∑ k ∈ s, w k * y k * Cov(X, D k)`
with every square integrable `X`. When `Cov(X, D k) = Cov(Y, η k)` for all `k`, the covariance of `X` with the dual sum
over `{0, …, n - 1}` evaluated at the regressors, `y = (η k ω')_k`, is the partial linear regression of `Y` on
`η 0, …, η (n - 1)` at `ω'`.

Along indices `ns j` whose blocks carry weights `∑_{ns j ≤ k < ns (j + 1)} w k * E[(D k)²] ≤ 4⁻ʲ`, the dual sums
evaluated at the regressors form, for almost every `ω'`, a Cauchy sequence in `L²`: the averaged squared `L²` norm of
the `j`-th block is at most `4⁻ʲ`, so `∑ⱼ 2ʲ ‖block j‖² < ∞` almost surely, and `‖block j‖ ≤ 2ʲ ‖block j‖² + 2⁻ʲ`.

## Main results

* `LatticeProb.Gauss.covariance_dualSum_right`: covariance with a dual sum.
* `LatticeProb.Gauss.covariance_dualSum_eq_partialRegression`: the partial linear regressions as covariances with dual
  sums evaluated at the regressors.
* `LatticeProb.Gauss.integral_dualSum_sq`: the second moment of a dual sum is a quadratic form in its coefficients.
* `LatticeProb.Gauss.ae_summable_of_summable_integral`: nonnegative integrable functions with summable integrals are
  almost everywhere summable.
* `LatticeProb.Gauss.ae_cauchy_dualSum`: the dual sums evaluated at the regressors are almost surely Cauchy in `L²`
  along a fast subsequence.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite block sum of a nonnegative summable sequence is bounded by the tail sum from the start of the block. -/
theorem sum_Ico_le_tsum_nat_add {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hsum : Summable c) (a b : ℕ) :
    ∑ k ∈ Finset.Ico a b, c k ≤ ∑' k, c (k + a) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [add_comm a]
  exact ((summable_nat_add_iff a).mpr hsum).sum_le_tsum _ fun k _ => hc _

/-- Dual sums of square integrable random variables are square integrable. -/
theorem memLp_dualSum {η D : ℕ → Ω → ℝ} (hD : ∀ k, MemLp (D k) 2 P) (s : Finset ℕ) (y : ℕ → ℝ) :
    MemLp (fun ω => dualSum P η D s y ω) 2 P := by
  unfold dualSum
  exact memLp_finsetSum s fun k _ => (hD k).const_mul _

/-- **Covariance with a dual sum.** `Cov(X, ∑ k ∈ s, w k * y k * D k) = ∑ k ∈ s, w k * y k * Cov(X, D k)`. -/
theorem covariance_dualSum_right [IsFiniteMeasure P] {η D : ℕ → Ω → ℝ} {X : Ω → ℝ} (hX : MemLp X 2 P)
    (hD : ∀ k, MemLp (D k) 2 P) (s : Finset ℕ) (y : ℕ → ℝ) :
    cov[X, fun ω => dualSum P η D s y ω; P] = ∑ k ∈ s, (Var[η k; P])⁻¹ * y k * cov[X, D k; P] := by
  rw [covariance_comm X]
  refine (covariance_fun_sum_const_mul_left (s := s) (fun k _ => hD k) hX
    fun k => (Var[η k; P])⁻¹ * y k).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [covariance_comm (D k)]

/-- **Partial regressions as covariances with dual sums.** If `Cov(X, D k) = Cov(Y, η k)` for every `k`, then the
covariance of `X` with the dual sum over `{0, …, n - 1}` evaluated at the regressors `(η k ω')_k` is the partial linear
regression of `Y` on `η 0, …, η (n - 1)` at `ω'`. -/
theorem covariance_dualSum_eq_partialRegression [IsFiniteMeasure P] {η D : ℕ → Ω → ℝ} {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hD : ∀ k, MemLp (D k) 2 P) (hXD : ∀ k, cov[X, D k; P] = cov[Y, η k; P]) (n : ℕ)
    (ω' : Ω) :
    cov[X, fun ω => dualSum P η D (Finset.range n) (fun k => η k ω') ω; P] = partialRegression P Y η n ω' := by
  rw [covariance_dualSum_right hX hD]
  simp only [partialRegression]
  exact Finset.sum_congr rfl fun k _ => by rw [hXD k]; ring

/-- **Second moment of a dual sum.** `E[(∑ k ∈ s, w k * y k * D k)²] = ∑ k, l ∈ s, w k * w l * E[D k * D l] * y k * y l`,
a quadratic form in the coefficients `y`. -/
theorem integral_dualSum_sq {η D : ℕ → Ω → ℝ} (hD : ∀ k, MemLp (D k) 2 P) (s : Finset ℕ) (y : ℕ → ℝ) :
    ∫ ω, dualSum P η D s y ω ^ 2 ∂P =
      ∑ k ∈ s, ∑ l ∈ s, ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * ∫ ω, D k ω * D l ω ∂P) * (y k * y l) := by
  have hsq : ∀ ω, dualSum P η D s y ω ^ 2 =
      ∑ k ∈ s, ∑ l ∈ s, ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * (y k * y l)) * (D k ω * D l ω) := by
    intro ω
    simp only [dualSum, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hint : ∀ k l, Integrable (fun ω => (Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * (y k * y l) *
      (D k ω * D l ω)) P := fun k l => ((hD k).integrable_mul (hD l)).const_mul _
  simp_rw [hsq]
  rw [integral_finsetSum s fun k _ => integrable_finsetSum s fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum s fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  ring

/-- **Summable integrals give almost everywhere summability.** Nonnegative integrable functions whose integrals are
summable are summable at almost every point. -/
theorem ae_summable_of_summable_integral {G : ℕ → Ω → ℝ} (hG : ∀ j, Integrable (G j) P)
    (hG0 : ∀ j ω, 0 ≤ G j ω) (hsum : Summable fun j => ∫ ω, G j ω ∂P) :
    ∀ᵐ ω ∂P, Summable fun j => G j ω := by
  have hmeas : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal (G j ω)) P := fun j =>
    (hG j).aemeasurable.ennreal_ofReal
  have hFm : AEMeasurable (fun ω => ∑' j, ENNReal.ofReal (G j ω)) P := AEMeasurable.tsum hmeas
  have hlint : ∫⁻ ω, ∑' j, ENNReal.ofReal (G j ω) ∂P ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have heq : ∀ j, ∫⁻ ω, ENNReal.ofReal (G j ω) ∂P = ENNReal.ofReal (∫ ω, G j ω ∂P) := fun j =>
      (ofReal_integral_eq_lintegral_ofReal (hG j) (Eventually.of_forall fun ω => hG0 j ω)).symm
    simp only [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun ω => hG0 j ω) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' hFm hlint] with ω hω
  exact (ENNReal.summable_toReal hω.ne).congr fun j => ENNReal.toReal_ofReal (hG0 j ω)

/-- **The dual sums are almost surely Cauchy in `L²` along a fast subsequence.** Let `η` be pairwise uncorrelated
centred square integrable random variables, `D` square integrable, and `ns` monotone indices whose blocks satisfy
`∑_{ns j ≤ k < ns (j + 1)} (Var[η k])⁻¹ * E[(D k)²] ≤ 4⁻ʲ`. Then for almost every `ω'` the dual sums over
`{0, …, ns j - 1}` evaluated at the regressors `(η k ω')_k` form a Cauchy sequence in `L²(P)`. -/
theorem ae_cauchy_dualSum [IsProbabilityMeasure P] {η D : ℕ → Ω → ℝ}
    (hη : ∀ k, MemLp (η k) 2 P) (hcen : ∀ k, P[η k] = 0) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0)
    (hD : ∀ k, MemLp (D k) 2 P) {ns : ℕ → ℕ} (hns : Monotone ns)
    (hblock : ∀ j, ∑ k ∈ Finset.Ico (ns j) (ns (j + 1)), (Var[η k; P])⁻¹ * ∫ ω, D k ω ^ 2 ∂P ≤ (1 / 4 : ℝ) ^ j) :
    ∀ᵐ ω' ∂P, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      ∫ ω, (dualSum P η D (Finset.range (ns n)) (fun k => η k ω') ω -
        dualSum P η D (Finset.range (ns m)) (fun k => η k ω') ω) ^ 2 ∂P < ε := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Ω → ℝ, G = fun j ω' =>
      ∫ ω, dualSum P η D (Finset.Ico (ns j) (ns (j + 1))) (fun k => η k ω') ω ^ 2 ∂P := ⟨_, rfl⟩
  have hG0 : ∀ j ω', 0 ≤ G j ω' := fun j ω' => by
    simp only [hG]
    exact integral_nonneg fun ω => sq_nonneg _
  have hGint : ∀ j, Integrable (G j) P := by
    intro j
    have hfun : G j = fun ω' => ∑ k ∈ Finset.Ico (ns j) (ns (j + 1)), ∑ l ∈ Finset.Ico (ns j) (ns (j + 1)),
        ((Var[η k; P])⁻¹ * (Var[η l; P])⁻¹ * ∫ ω, D k ω * D l ω ∂P) * (η k ω' * η l ω') := by
      simp only [hG]
      exact funext fun ω' => integral_dualSum_sq hD _ _
    rw [hfun]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      ((hη k).integrable_mul (hη l)).const_mul _
  have hGle : ∀ j, ∫ ω', G j ω' ∂P ≤ (1 / 4 : ℝ) ^ j := fun j => by
    simp only [hG]
    exact (integral_integral_dualSum_sq hη hcen horth hD _).le.trans (hblock j)
  have hsum2 : Summable fun j => ∫ ω', (2 : ℝ) ^ j * G j ω' ∂P := by
    refine Summable.of_nonneg_of_le
      (fun j => integral_nonneg fun ω' => mul_nonneg (by positivity) (hG0 j ω')) (fun j => ?_)
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    rw [integral_const_mul]
    calc (2 : ℝ) ^ j * ∫ ω', G j ω' ∂P ≤ 2 ^ j * (1 / 4) ^ j :=
          mul_le_mul_of_nonneg_left (hGle j) (by positivity)
      _ = (1 / 2) ^ j := by rw [← mul_pow]; norm_num
  filter_upwards [ae_summable_of_summable_integral (fun j => (hGint j).const_mul ((2 : ℝ) ^ j))
    (fun j ω' => mul_nonneg (by positivity) (hG0 j ω')) hsum2] with ω' hω'
  have hω'' : Summable fun j => (2 : ℝ) ^ j * G j ω' := hω'
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℕ → Ω → ℝ,
      ζ = fun j ω => dualSum P η D (Finset.range (ns j)) (fun k => η k ω') ω := ⟨_, rfl⟩
  have hζm : ∀ j, MemLp (ζ j) 2 P := fun j => by
    rw [hζ]
    exact memLp_dualSum hD _ _
  have hdist : ∀ n m, dist ((hζm n).toLp (ζ n)) ((hζm m).toLp (ζ m)) ^ 2 =
      ∫ ω, (ζ n ω - ζ m ω) ^ 2 ∂P := by
    intro n m
    rw [dist_eq_norm, ← MemLp.toLp_sub (hζm n) (hζm m), norm_toLp_two_sq]
    rfl
  have hstep : ∀ j, dist ((hζm j).toLp (ζ j)) ((hζm (j + 1)).toLp (ζ (j + 1))) ^ 2 = G j ω' := by
    intro j
    rw [hdist, hG]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hζ, dualSum]
    rw [Finset.sum_Ico_eq_sub _ (hns (Nat.le_succ j))]
    ring
  have key : ∀ a t d : ℝ, 0 < a → a * t = 1 → d ≤ a * d ^ 2 + t := fun a t d ha hat => by
    nlinarith [sq_nonneg (a * d - 1 / 2)]
  have hdsum : Summable fun j => dist ((hζm j).toLp (ζ j)) ((hζm (j + 1)).toLp (ζ (j + 1))) := by
    refine Summable.of_nonneg_of_le (fun j => dist_nonneg) (fun j => ?_)
      (hω''.add (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)))
    show _ ≤ (2 : ℝ) ^ j * G j ω' + (1 / 2) ^ j
    rw [← hstep j]
    exact key _ _ _ (by positivity) (by rw [← mul_pow]; norm_num)
  have hcs : CauchySeq fun j => (hζm j).toLp (ζ j) := cauchySeq_of_summable_dist hdsum
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcs (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hlt := (Real.lt_sqrt dist_nonneg).1 (hN n hn m hm)
  rw [hdist n m] at hlt
  subst hζ
  exact hlt

end LatticeProb.Gauss
