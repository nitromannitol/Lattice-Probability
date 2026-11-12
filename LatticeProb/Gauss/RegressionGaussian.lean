import LatticeProb.Gauss.RegressionResidual
import LatticeProb.Gauss.CameronMartinLimitShift

/-!
# The residuals of the linear regression on a Gaussian process

Let `Z = (Z t)_{t ∈ ι}` be a centred Gaussian process and let `η k = Z (e k)`, `k ∈ ℕ`, be pairwise uncorrelated
coordinates of it. For every coordinate `Z (x i)` the partial linear regressions on `η 0, …, η (n - 1)` converge in
`L²` and almost surely along a subsequence (`LatticeProb.Gauss.exists_tendsto_partialRegression`). This file shows
that the limit is almost surely a measurable function `m i` of the sequence `η`, and that the residuals
`Z (x i) - m i (η)` lie in a centred Gaussian space containing every coordinate of `Z`. In particular the residuals
form, jointly with the process, a centred Gaussian process, and they are independent of the sequence `η`. This is the
Gaussian form of the statement that, given `η`, the family `(Z (x i))_i` is distributed as the residual family shifted
by the conditional mean `(m i (η))_i`.

## Main results

* `LatticeProb.Gauss.exists_measurable_tendsto_partialRegression`: an almost sure limit of partial regressions along a
  subsequence is almost surely a measurable function of the regressors.
* `LatticeProb.Gauss.exists_regression_residual`: the regression functions `m i`, the `L²` convergence of the partial
  regressions to `m i (η)`, a centred Gaussian space containing the process and the residuals, and the independence of
  the residual family and the sequence `η`.
-/

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.GaussianClosure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An almost sure limit of partial linear regressions along a subsequence is almost surely a measurable function of
the sequence of regressors. -/
theorem exists_measurable_tendsto_partialRegression {Y ρ : Ω → ℝ} {η : ℕ → Ω → ℝ} (hη : ∀ k, Measurable (η k))
    {ns : ℕ → ℕ} (hae : ∀ᵐ ω ∂P, Tendsto (fun j => partialRegression P Y η (ns j) ω) atTop (𝓝 (ρ ω))) :
    ∃ m : (ℕ → ℝ) → ℝ, Measurable m ∧
      ∀ᵐ ω ∂P, Tendsto (fun j => partialRegression P Y η (ns j) ω) atTop (𝓝 (m fun k => η k ω)) := by
  set F : ℕ → (ℕ → ℝ) → ℝ := fun j y =>
    ∑ k ∈ Finset.range (ns j), (Var[η k; P])⁻¹ * cov[Y, η k; P] * y k with hF
  have hFm : ∀ j, Measurable (F j) := fun j =>
    Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).const_mul _
  have hηm : Measurable fun ω k => η k ω := measurable_pi_iff.mpr hη
  have hS : MeasurableSet {y : ℕ → ℝ | ∃ c, Tendsto (fun j => F j y) atTop (𝓝 c)} :=
    StronglyMeasurable.measurableSet_exists_tendsto fun j => (hFm j).stronglyMeasurable
  have hex : ∀ᵐ y ∂(P.map fun ω k => η k ω), ∃ c, Tendsto (fun j => F j y) atTop (𝓝 c) := by
    rw [ae_map_iff hηm.aemeasurable hS]
    filter_upwards [hae] with ω hω
    exact ⟨ρ ω, hω⟩
  obtain ⟨m, hm, hlim⟩ := measurable_limit_of_tendsto_metrizable_ae (fun j => (hFm j).aemeasurable) hex
  exact ⟨m, hm, ae_of_ae_map hηm.aemeasurable hlim⟩

/-- A partial linear regression on coordinates of a process is a linear combination of coordinates. -/
theorem partialRegression_mem_span_range {ι : Type*} (Z : ι → Ω → ℝ) (Y : Ω → ℝ) (e : ℕ → ι) (n : ℕ) :
    partialRegression P Y (fun k => Z (e k)) n ∈ Submodule.span ℝ (Set.range Z) := by
  have h : partialRegression P Y (fun k => Z (e k)) n =
      ∑ k ∈ Finset.range n, ((Var[Z (e k); P])⁻¹ * cov[Y, Z (e k); P]) • Z (e k) := by
    funext ω
    simp [partialRegression, Finset.sum_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)

/-- **Regression residuals of a Gaussian process.** Let `Z` be a centred Gaussian process and let `η k = Z (e k)`
be pairwise uncorrelated coordinates. There are measurable functions `m i` on sequences such that the partial linear
regressions of `Z (x i)` on `η` converge in `L²` to `m i (η)`, the residuals `Z (x i) - m i (η)` and all coordinates of
`Z` lie in one centred Gaussian space, and the residual family is independent of the sequence `η`. -/
theorem exists_regression_residual [IsProbabilityMeasure P] {ι κ : Type*} {Z : ι → Ω → ℝ}
    (hZ : IsGaussianProcess Z P) (hZm : ∀ t, Measurable (Z t)) (hcen : ∀ t, P[Z t] = 0) (x : κ → ι)
    (e : ℕ → ι) (horth : ∀ k l, k ≠ l → cov[Z (e k), Z (e l); P] = 0) :
    ∃ m : κ → (ℕ → ℝ) → ℝ, (∀ i, Measurable (m i)) ∧
      (∀ i, MemLp (fun ω => m i fun k => Z (e k) ω) 2 P) ∧
      (∀ i, Tendsto (fun n => ∫ ω, (partialRegression P (Z (x i)) (fun k => Z (e k)) n ω -
        m i (fun k => Z (e k) ω)) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∃ M : Submodule ℝ (Ω → ℝ), IsCentredGaussianSpace P M ∧ (∀ t, Z t ∈ M) ∧
        ∀ i, (fun ω => Z (x i) ω - m i fun k => Z (e k) ω) ∈ M) ∧
      IndepFun (fun ω i => Z (x i) ω - m i fun k => Z (e k) ω) (fun ω k => Z (e k) ω) P := by
  have hZ2 : ∀ t, MemLp (Z t) 2 P := fun t => (hZ.hasGaussianLaw_eval t).memLp_two
  choose ρ ns _ hρ2 hρL2 _ hρae using fun i =>
    exists_tendsto_partialRegression (hZ2 (x i)) (fun k => hZ2 (e k)) (fun k => hcen (e k)) horth
  choose m hm hmae using fun i =>
    exists_measurable_tendsto_partialRegression (fun k => hZm (e k)) (hρae i)
  have hηm : Measurable fun ω k => Z (e k) ω := measurable_pi_iff.mpr fun k => hZm (e k)
  set ρ' : κ → Ω → ℝ := fun i ω => m i fun k => Z (e k) ω with hρ'
  have hρ'm : ∀ i, Measurable (ρ' i) := fun i => (hm i).comp hηm
  have hρeq : ∀ i, ρ i =ᵐ[P] ρ' i := by
    intro i
    filter_upwards [hρae i, hmae i] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  have hρ'2 : ∀ i, MemLp (ρ' i) 2 P := fun i => (hρ2 i).ae_eq (hρeq i)
  have hL2 : ∀ i, Tendsto (fun n => ∫ ω, (partialRegression P (Z (x i)) (fun k => Z (e k)) n ω -
      ρ' i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro i
    refine (hρL2 i).congr fun n => integral_congr_ae ?_
    filter_upwards [hρeq i] with ω hω
    rw [hω]
  -- the Gaussian space spanned by the process and the limits of the regressions
  set M0 : Submodule ℝ (Ω → ℝ) := Submodule.span ℝ (Set.range Z) with hM0
  have hM0g : IsCentredGaussianSpace P M0 := isCentredGaussianSpace_span_range hZ hZm hcen
  have hlim : ∀ i, IsAeLimitOf P M0 (ρ' i) := fun i =>
    ⟨fun j => partialRegression P (Z (x i)) (fun k => Z (e k)) (ns i j),
      fun j => partialRegression_mem_span_range Z (Z (x i)) e (ns i j), hmae i⟩
  have hMg := isCentredGaussianSpace_sup_span_range hM0g ρ' hρ'm hlim
  set M : Submodule ℝ (Ω → ℝ) := M0 ⊔ Submodule.span ℝ (Set.range ρ') with hM
  have hZmem : ∀ t, Z t ∈ M := fun t => Submodule.mem_sup_left (Submodule.subset_span ⟨t, rfl⟩)
  have hRmem : ∀ i, (fun ω => Z (x i) ω - ρ' i ω) ∈ M := fun i =>
    M.sub_mem (hZmem (x i)) (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
  have hRm : ∀ i, Measurable fun ω => Z (x i) ω - ρ' i ω := fun i => (hZm (x i)).sub (hρ'm i)
  have hW : IsGaussianProcess (Sum.elim (fun i ω => Z (x i) ω - ρ' i ω) fun k => Z (e k)) P := by
    refine isGaussianProcess_of_isCentredGaussianSpace hMg fun s => ?_
    cases s with
    | inl i => exact hRmem i
    | inr k => exact hZmem (e k)
  refine ⟨m, hm, hρ'2, hL2, ⟨M, hMg, hZmem, hRmem⟩, ?_⟩
  exact hW.indepFun_of_covariance_eq_zero (fun i => (hRm i).aemeasurable)
    (fun k => (hZm (e k)).aemeasurable) fun i k =>
      covariance_sub_limit_regression_eq_zero (hZ2 (x i)) (fun k => hZ2 (e k)) horth (hρ'2 i) (hL2 i) k

end LatticeProb.Gauss
