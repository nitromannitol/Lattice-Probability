import LatticeProb.Gauss.GaussianSpaceShift

/-!
# Mutual absolute continuity of the conditional laws of a Gaussian family

Let `Z` be a centred Gaussian process, `(X_i)_i = (Z (x i))_i` a countable family of its coordinates and
`(η_k)_k = (Z (e k))_k` a countable family of pairwise uncorrelated coordinates (the regressors). Suppose there is
a dual family `(D_k)_k = (Z (d k))_k` which is uncorrelated with every regressor, has the same covariances with the
`X_i` as the regressors, and satisfies `∑_k Var(D_k) / Var(η_k) < ∞`.

Then the conditional law of `(X_i)_i` given `(η_k)_k` is, for almost every value of the regressors, the law of the
regression residual shifted by the limit regression, and the shift lies in the Cameron-Martin space of the residual:
the dual sums `∑_{k < n} Var(η_k)⁻¹ η_k(ω') D_k` form an `L²`-Cauchy sequence whose covariances with the residuals
converge to the limit regression at `ω'`. Consequently all these conditional laws have the same null sets, and an
event of the form `{X ∈ S} ∩ {η ∈ S'}` is null only if `{X ∈ S}` or `{η ∈ S'}` is null.

## Main results

* `LatticeProb.Gauss.ae_measure_residual_add_eq_zero_iff`: for almost every `ω'`, a measurable path set is null for
  the residual family iff it is null for its shift by the limit regression evaluated at the regressors at `ω'`.
* `LatticeProb.Gauss.measure_inter_eq_zero_of_dual_family`: the dichotomy for `{X ∈ S} ∩ {η ∈ S'}`.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.GaussianClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For a centred Gaussian process with pairwise uncorrelated regressors `Z (e k)` and a dual family `Z (d k)`
(uncorrelated with the regressors, with the covariances of the regressors against the `Z (x i)`, and
`∑ Var(Z (d k)) / Var(Z (e k)) < ∞`), there are measurable limit regressions `m i` such that the residuals
`Z (x i) - m i (Z (e ·))` are independent of the regressors and, for almost every `ω'`, every measurable path set is
null for the residual family iff it is null for its shift by `(m i (Z (e ·) ω'))_i`. -/
theorem ae_measure_residual_add_eq_zero_iff [IsProbabilityMeasure P] {ι : Type*} {Z : ι → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hZm : ∀ t, Measurable (Z t)) (hcen : ∀ t, P[Z t] = 0) (x e d : ℕ → ι)
    (horth : ∀ k l, k ≠ l → cov[Z (e k), Z (e l); P] = 0) (hde : ∀ k l, cov[Z (d k), Z (e l); P] = 0)
    (hdual : ∀ i k, cov[Z (x i), Z (d k); P] = cov[Z (x i), Z (e k); P])
    (hsum : Summable fun k => (Var[Z (e k); P])⁻¹ * Var[Z (d k); P]) :
    ∃ m : ℕ → (ℕ → ℝ) → ℝ, (∀ i, Measurable (m i)) ∧
      IndepFun (fun ω i => Z (x i) ω - m i fun k => Z (e k) ω) (fun ω k => Z (e k) ω) P ∧
      ∀ᵐ ω' ∂P, ∀ S : Set (ℕ → ℝ), MeasurableSet S →
        (P {ω | (fun i => Z (x i) ω - m i (fun k => Z (e k) ω) + m i fun k => Z (e k) ω') ∈ S} = 0 ↔
          P {ω | (fun i => Z (x i) ω - m i fun k => Z (e k) ω) ∈ S} = 0) := by
  have hZ2 : ∀ t, MemLp (Z t) 2 P := fun t => (hZ.hasGaussianLaw_eval t).memLp_two
  obtain ⟨m, hm, hmL2, htend, ⟨M, hM, hZM, hRM⟩, hind⟩ := exists_regression_residual hZ hZm hcen x e horth
  refine ⟨m, hm, hind, ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun k => (Var[Z (e k); P])⁻¹ * Var[Z (d k); P] := ⟨_, rfl⟩
  rw [← hc] at hsum
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    rw [hc]; exact mul_nonneg (inv_nonneg.mpr (variance_nonneg _ _)) (variance_nonneg _ _)
  -- a common fast subsequence for the tails of `∑ c` and for the regression errors
  obtain ⟨ns, hns, hbound⟩ := exists_strictMono_forall_abs_le_of_tendsto
    (a := fun i n => if i = 0 then ∑' k, c (k + n) else
      ∫ ω, (partialRegression P (Z (x (i - 1))) (fun k => Z (e k)) n ω -
        m (i - 1) (fun k => Z (e k) ω)) ^ 2 ∂P) (fun i => by
      rcases i with _ | i
      · simpa using tendsto_sum_nat_add c
      · simpa using htend i)
  have htail : ∀ j, ∑' k, c (k + ns j) ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    have h := hbound 0 j (Nat.zero_le j)
    beta_reduce at h
    rw [ite_eq_left rfl] at h
    exact (le_abs_self _).trans h
  have herr : ∀ i j, i + 1 ≤ j → ∫ ω, (partialRegression P (Z (x i)) (fun k => Z (e k)) (ns j) ω -
      m i (fun k => Z (e k) ω)) ^ 2 ∂P ≤ (1 / 4 : ℝ) ^ j := by
    intro i j hij
    have h := hbound (i + 1) j hij
    beta_reduce at h
    rw [ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel] at h
    exact (le_abs_self _).trans h
  -- the dual sums at the regressors are almost surely `L²`-Cauchy along `ns`
  have hDvar : ∀ k, ∫ ω, Z (d k) ω ^ 2 ∂P = Var[Z (d k); P] := fun k =>
    (variance_of_integral_eq_zero (hZm (d k)).aemeasurable (hcen (d k))).symm
  have hblock : ∀ j, ∑ k ∈ Finset.Ico (ns j) (ns (j + 1)),
      (Var[Z (e k); P])⁻¹ * ∫ ω, Z (d k) ω ^ 2 ∂P ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      ((sum_Ico_le_tsum_nat_add hc0 hsum (ns j) (ns (j + 1))).trans (htail j))
    rw [hc, hDvar]
  have hcauchy := ae_cauchy_dualSum (P := P) (η := fun k => Z (e k)) (D := fun k => Z (d k))
    (fun k => hZ2 (e k)) (fun k => hcen (e k)) horth (fun k => hZ2 (d k)) hns.monotone hblock
  -- the partial regressions converge almost surely along `ns` to the limit regressions
  have hconv : ∀ i, ∀ᵐ ω' ∂P, Tendsto (fun j => partialRegression P (Z (x i)) (fun k => Z (e k)) (ns j) ω')
      atTop (𝓝 (m i fun k => Z (e k) ω')) := by
    intro i
    have hG : ∀ j, Integrable (fun ω => (partialRegression P (Z (x i)) (fun k => Z (e k)) (ns j) ω -
        m i (fun k => Z (e k) ω)) ^ 2) P := fun j =>
      ((memLp_partialRegression (fun k => hZ2 (e k)) _ _).sub (hmL2 i)).integrable_sq
    have hGs : Summable fun j => ∫ ω, (partialRegression P (Z (x i)) (fun k => Z (e k)) (ns j) ω -
        m i (fun k => Z (e k) ω)) ^ 2 ∂P := by
      refine Summable.of_norm_bounded_eventually_nat
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)) ?_
      filter_upwards [eventually_ge_atTop (i + 1)] with j hj
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)]
      exact herr i j hj
    filter_upwards [ae_summable_of_summable_integral hG (fun j ω => sq_nonneg _) hGs] with ω' hω'
    have h := (Real.continuous_sqrt.tendsto 0).comp hω'.tendsto_atTop_zero
    rw [Real.sqrt_zero] at h
    refine tendsto_iff_dist_tendsto_zero.mpr (h.congr fun j => ?_)
    simp only [Function.comp_apply, Real.sqrt_sq_eq_abs, Real.dist_eq]
  have hRL2 : ∀ i, MemLp (fun ω => Z (x i) ω - m i fun k => Z (e k) ω) 2 P := fun i =>
    (hZ2 (x i)).sub (hmL2 i)
  have hXD : ∀ i k, cov[fun ω => Z (x i) ω - m i (fun k => Z (e k) ω), Z (d k); P] =
      cov[Z (x i), Z (e k); P] := fun i k =>
    (covariance_sub_limit_regression_of_covariance_eq_zero (hZ2 (x i)) (fun l => hZ2 (e l)) (hmL2 i)
      (hZ2 (d k)) (htend i) fun l => (covariance_comm (Z (e l)) (Z (d k))).trans (hde k l)).trans (hdual i k)
  filter_upwards [hcauchy, ae_all_iff.mpr hconv] with ω' hC hT S hS
  refine measure_add_eq_zero_iff_of_tendsto_covariance_of_cauchy hM
    (R := fun i ω => Z (x i) ω - m i fun k => Z (e k) ω)
    (ζ := fun n ω => dualSum P (fun k => Z (e k)) (fun k => Z (d k)) (Finset.range (ns n))
      (fun k => Z (e k) ω') ω)
    (c := fun i => m i fun k => Z (e k) ω') hRM (fun n => ?_) hC (fun i => ?_) hS
  · have hsumM : (fun ω => dualSum P (fun k => Z (e k)) (fun k => Z (d k)) (Finset.range (ns n))
        (fun k => Z (e k) ω') ω) =
        ∑ k ∈ Finset.range (ns n), ((Var[Z (e k); P])⁻¹ * Z (e k) ω') • Z (d k) := by
      funext ω
      simp [dualSum, Finset.sum_apply, smul_eq_mul]
    rw [hsumM]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hZM _)
  · exact (hT i).congr fun n => (covariance_dualSum_eq_partialRegression (η := fun k => Z (e k))
      (Y := Z (x i)) (hRL2 i) (fun k => hZ2 (d k)) (hXD i) (ns n) ω').symm

/-- **Conditional equivalence for a Gaussian family with a dual family.** Under the hypotheses of
`ae_measure_residual_add_eq_zero_iff`, if `{(Z (x i))_i ∈ S} ∩ {(Z (e k))_k ∈ S'}` is null then
`{(Z (x i))_i ∈ S}` or `{(Z (e k))_k ∈ S'}` is null. -/
theorem measure_inter_eq_zero_of_dual_family [IsProbabilityMeasure P] {ι : Type*} {Z : ι → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hZm : ∀ t, Measurable (Z t)) (hcen : ∀ t, P[Z t] = 0) (x e d : ℕ → ι)
    (horth : ∀ k l, k ≠ l → cov[Z (e k), Z (e l); P] = 0) (hde : ∀ k l, cov[Z (d k), Z (e l); P] = 0)
    (hdual : ∀ i k, cov[Z (x i), Z (d k); P] = cov[Z (x i), Z (e k); P])
    (hsum : Summable fun k => (Var[Z (e k); P])⁻¹ * Var[Z (d k); P])
    {S S' : Set (ℕ → ℝ)} (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (h0 : P ({ω | (fun i => Z (x i) ω) ∈ S} ∩ {ω | (fun k => Z (e k) ω) ∈ S'}) = 0) :
    P {ω | (fun i => Z (x i) ω) ∈ S} = 0 ∨ P {ω | (fun k => Z (e k) ω) ∈ S'} = 0 := by
  obtain ⟨m, hm, hind, hae⟩ := ae_measure_residual_add_eq_zero_iff hZ hZm hcen x e d horth hde hdual hsum
  have hη : Measurable fun ω k => Z (e k) ω := measurable_pi_iff.mpr fun k => hZm (e k)
  have hR : Measurable fun ω i => Z (x i) ω - m i fun k => Z (e k) ω :=
    measurable_pi_iff.mpr fun i => (hZm (x i)).sub ((hm i).comp hη)
  have hg : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => fun i => p.1 i + m i p.2 :=
    measurable_pi_iff.mpr fun i =>
      ((measurable_pi_apply i).comp measurable_fst).add ((hm i).comp measurable_snd)
  have hT : MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | (fun i => p.1 i + m i p.2) ∈ S ∧ p.2 ∈ S'} :=
    (hg hS).inter (measurable_snd hS')
  have hT0 : MeasurableSet {p : (ℕ → ℝ) × (ℕ → ℝ) | (fun i => p.1 i + m i p.2) ∈ S} := hg hS
  -- Fubini over the independent pair (residuals, regressors)
  have hF : ∫⁻ ω', P {ω | (fun i => Z (x i) ω - m i (fun k => Z (e k) ω) + m i fun k => Z (e k) ω') ∈ S ∧
      (fun k => Z (e k) ω') ∈ S'} ∂P = 0 := by
    refine ((measure_pair_eq_lintegral_of_indepFun hR hη hind hT).symm.trans ?_).trans h0
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, sub_add_cancel]
  have hF0 : P {ω | (fun i => Z (x i) ω) ∈ S} =
      ∫⁻ ω', P {ω | (fun i => Z (x i) ω - m i (fun k => Z (e k) ω) + m i fun k => Z (e k) ω') ∈ S} ∂P := by
    refine Eq.trans ?_ (measure_pair_eq_lintegral_of_indepFun hR hη hind hT0)
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, sub_add_cancel]
  have hq : Measurable fun q : Ω × (ℕ → ℝ) => fun i => Z (x i) q.1 - m i (fun k => Z (e k) q.1) + m i q.2 :=
    measurable_pi_iff.mpr fun i => (((hZm (x i)).comp measurable_fst).sub
      ((hm i).comp (hη.comp measurable_fst))).add ((hm i).comp measurable_snd)
  have hFm : Measurable fun ω' => P {ω | (fun i => Z (x i) ω - m i (fun k => Z (e k) ω) +
      m i fun k => Z (e k) ω') ∈ S ∧ (fun k => Z (e k) ω') ∈ S'} :=
    (measurable_measure_prodMk_right (μ := P) ((hq hS).inter (measurable_snd hS'))).comp hη
  rw [or_iff_not_imp_right]
  intro hS'0
  by_contra hX0
  apply hS'0
  have hbad : ∀ᵐ ω' ∂P, (fun k => Z (e k) ω') ∈ S' → False := by
    filter_upwards [(lintegral_eq_zero_iff hFm).mp hF, hae] with ω' hf hA hω'
    apply hX0
    have h1 : P {ω | (fun i => Z (x i) ω - m i (fun k => Z (e k) ω) + m i fun k => Z (e k) ω') ∈ S} = 0 := by
      simpa only [Pi.zero_apply, hω', and_true] using hf
    have h2 := (hA S hS).mp h1
    rw [hF0]
    exact (lintegral_congr_ae (g := fun _ => 0) (hae.mono fun ω'' hA'' => (hA'' S hS).mpr h2)).trans
      lintegral_zero
  have hnull := ae_iff.mp hbad
  refine measure_mono_null ?_ hnull
  intro ω' hω' hb
  exact hb hω'

end LatticeProb.Gauss
