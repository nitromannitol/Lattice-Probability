/-
# Normal comparison (Li--Shao): left-continuity of the orthant probability at the endpoint

Route: `scratch/pk/normalcompare-route.md`, item 8a.  The interpolation of the Li--Shao route
runs over the smart path `S_t = normalComparisonSmartPath v S t = (1 - t) • (v • 1) + t • S`
on `[0, T]`, `T < 1`, where `S_t` is positive definite and has a density.  At the endpoint
`t = 1` the matrix `S` is only positive semidefinite (possibly singular, no density), so the
final step needs the Gaussian orthant probability to be left-continuous at `t = 1`.

* `frontier_orthant_subset` : the frontier of `{y | ∀ i, y i ≤ b i}` lies in the union of the
  hyperplanes `{y i = b i}`.
* `multivariateGaussian_orthant_frontier_null` : for `S` positive semidefinite with constant
  diagonal `v > 0`, the Gaussian `N(0, S)` gives zero mass to that frontier (each coordinate is
  `N(0, v)`, which has no atoms).
* `charFun_multivariateGaussian_zero`, `continuous_dotProduct_normalComparisonSmartPath` and
  `tendsto_charFun_multivariateGaussian_path` : the characteristic function of `N(0, S_t)` is
  `exp (-(1/2) ξᵀ S_t ξ)`, continuous in `t`.
* `multivariateGaussianProb` and `tendsto_multivariateGaussian_path_probabilityMeasure` :
  `N(0, S_t) ⇒ N(0, S)` weakly as `t → 1` within `[0, 1]` (Lévy's continuity theorem along
  sequences).
* `tendsto_multivariateGaussian_orthant_path_Icc` and
  `tendsto_multivariateGaussian_orthant_path` : the portmanteau theorem gives
  `N(0, S_t)(orthant) → N(0, S)(orthant)` as `t ↑ 1`.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonPath

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix

namespace LatticeProb

/-! ### The frontier of the orthant -/

/-- The frontier of the orthant `{y | ∀ i, y i ≤ b i}` lies in the union of the coordinate
hyperplanes `{y | y i = b i}`: the orthant is closed and contains the open set
`{y | ∀ i, y i < b i}`, so a frontier point lies in the orthant and not in that open set. -/
theorem frontier_orthant_subset {n : ℕ} (b : Fin n → ℝ) :
    frontier {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} ⊆ ⋃ i, {y | y i = b i} := by
  have hcl : IsClosed {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} := by
    have : {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} = ⋂ i, {y | y i ≤ b i} := by
      ext y; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  have hop : IsOpen {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i < b i} := by
    have : {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i < b i} = ⋂ i, {y | y i < b i} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const
  have hsub : {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i < b i} ⊆
      {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} := fun y hy i => (hy i).le
  intro y hy
  rw [frontier, hcl.closure_eq] at hy
  obtain ⟨hyle, hyint⟩ := hy
  by_contra hne
  apply hyint
  refine interior_maximal hsub hop fun i => ?_
  by_contra hlt
  exact hne (Set.mem_iUnion.2 ⟨i, le_antisymm (hyle i) (not_lt.1 hlt)⟩)

/-- **The frontier of the orthant is null for `N(0, S)` with constant diagonal `v > 0`.**
Each coordinate of `N(0, S)` is `N(0, v)`, which is absolutely continuous, so the hyperplane
`{y | y i = b i}` is null; the frontier lies in the finite union of these hyperplanes. -/
theorem multivariateGaussian_orthant_frontier_null {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (b : Fin n → ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      (frontier {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}) = 0 := by
  refine measure_mono_null (frontier_orthant_subset b) (measure_iUnion_null fun i => ?_)
  have hvne : (S i i).toNNReal ≠ 0 := by
    rw [hdiag i]
    exact (Real.toNNReal_pos.2 hv).ne'
  have hmp := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin n))) hS (i := i)
  have hpre : {y : EuclideanSpace ℝ (Fin n) | y i = b i} =
      (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' {b i} := rfl
  rw [hpre, ← Measure.map_apply hmp.measurable (measurableSet_singleton (b i)), hmp.map_eq]
  exact gaussianReal_absolutelyContinuous _ hvne (Real.volume_singleton)

/-! ### The characteristic function along the path -/

/-- The characteristic function of `N(0, S_t)` for `S_t` positive semidefinite:
`exp (-(1/2) ξᵀ S_t ξ)`. -/
theorem charFun_multivariateGaussian_zero {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (ξ : EuclideanSpace ℝ (Fin n)) :
    charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) ξ =
      Complex.exp (-(((ξ ⬝ᵥ S *ᵥ ξ : ℝ) : ℂ) / 2)) := by
  rw [charFun_multivariateGaussian hS]
  simp [sub_eq_add_neg]


/-- The quadratic form `ξᵀ S_t ξ` along the smart path is continuous in `t`. -/
theorem continuous_dotProduct_normalComparisonSmartPath {n : ℕ} (v : ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    Continuous fun t : ℝ => ξ ⬝ᵥ normalComparisonSmartPath v S t *ᵥ ξ := by
  have hM : Continuous fun t : ℝ => normalComparisonSmartPath v S t :=
    continuous_matrix fun i j => continuous_normalComparisonSmartPath_apply v S i j
  exact continuous_const.dotProduct (hM.matrix_mulVec continuous_const)

/-- The characteristic function of `N(0, S_t)` converges to that of `N(0, S)` as `t → 1`
within `[0, 1]`, where `S_t` is positive semidefinite. -/
theorem tendsto_charFun_multivariateGaussian_path {n : ℕ} {v : ℝ} (hv : 0 ≤ v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (ξ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (normalComparisonSmartPath v S t)) ξ)
      (𝓝[Set.Icc 0 1] 1)
      (𝓝 (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) ξ)) := by
  have hc : Continuous fun t : ℝ =>
      Complex.exp (-(((ξ ⬝ᵥ normalComparisonSmartPath v S t *ᵥ ξ : ℝ) : ℂ) / 2)) := by
    have := continuous_dotProduct_normalComparisonSmartPath v S ξ
    fun_prop
  have h1 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Icc (0 : ℝ) 1))
  rw [normalComparisonSmartPath_one, ← charFun_multivariateGaussian_zero hS] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (charFun_multivariateGaussian_zero
    (normalComparisonSmartPath_posSemidef hS hv ht) ξ).symm


/-! ### Weak convergence along the path -/

/-- The centred Gaussian `N(0, S)` on `EuclideanSpace ℝ (Fin n)` packaged as a
`ProbabilityMeasure`.  Every `multivariateGaussian` is a probability measure (a Gaussian
measure is one), so no hypothesis on `S` is needed. -/
noncomputable def multivariateGaussianProb {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S, inferInstance⟩

/-- The underlying measure of `multivariateGaussianProb S` is `N(0, S)`. -/
@[simp] theorem toMeasure_multivariateGaussianProb {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    (multivariateGaussianProb S : Measure (EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S := rfl

/-- **Weak convergence along the smart path.**  The centred Gaussians `N(0, S_t)`, packaged as
probability measures, converge weakly to `N(0, S)` as `t → 1` within `[0, 1]`.  The proof is
Lévy's continuity theorem along sequences; every `multivariateGaussian` is a probability
measure, so the packaging needs no hypothesis on `t`. -/
theorem tendsto_multivariateGaussian_path_probabilityMeasure {n : ℕ} {v : ℝ} (hv : 0 ≤ v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) :
    Tendsto (fun t : ℝ => multivariateGaussianProb (normalComparisonSmartPath v S t))
      (𝓝[Set.Icc 0 1] 1) (𝓝 (multivariateGaussianProb S)) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro x hx
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ξ => ?_
  exact (tendsto_charFun_multivariateGaussian_path hv hS ξ).comp hx

/-! ### The orthant probability at the endpoint -/

/-- **Left-continuity of the orthant probability at the endpoint, on `[0, 1]`.**  As `t → 1`
within `[0, 1]`, `N(0, S_t)(orthant) → N(0, S)(orthant)`, for `S` positive semidefinite with
constant diagonal `v > 0`.  The portmanteau theorem applies since the orthant has null frontier
for the limit law. -/
theorem tendsto_multivariateGaussian_orthant_path_Icc {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (b : Fin n → ℝ) :
    Tendsto
      (fun t : ℝ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (normalComparisonSmartPath v S t) {y | ∀ i, y i ≤ b i}).toReal)
      (𝓝[Set.Icc 0 1] 1)
      (𝓝 ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
        {y | ∀ i, y i ≤ b i}).toReal)) := by
  have hlim := tendsto_multivariateGaussian_path_probabilityMeasure hv.le hS
  have hfront := multivariateGaussian_orthant_frontier_null hv hS hdiag b
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hlim
    (E := {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i})
    ((ProbabilityMeasure.null_iff_toMeasure_null _ _).2 hfront)
  exact (NNReal.continuous_coe.tendsto _).comp key

/-- **Left-continuity of the orthant probability at the endpoint.**  As `t ↑ 1`,
`N(0, S_t)(orthant) → N(0, S)(orthant)`, for `S` positive semidefinite with constant diagonal
`v > 0`; here `S` itself may be singular, so `N(0, S)` has no density and the endpoint is not
reached by the density argument on `[0, T]`, `T < 1`. -/
theorem tendsto_multivariateGaussian_orthant_path {n : ℕ} {v : ℝ} (hv : 0 < v)
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) (hdiag : ∀ i, S i i = v)
    (b : Fin n → ℝ) :
    Filter.Tendsto
      (fun t : ℝ => (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (normalComparisonSmartPath v S t) {y | ∀ i, y i ≤ b i}).toReal)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
        {y | ∀ i, y i ≤ b i}).toReal)) := by
  refine (tendsto_multivariateGaussian_orthant_path_Icc hv hS hdiag b).mono_left ?_
  rw [nhdsWithin_le_iff]
  exact mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Set.Ioo_subset_Icc_self

end LatticeProb
