import Mathlib.LinearAlgebra.Pi
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# Laws of Gaussian processes are determined by mean and covariance

Let `X, Y : T → Ω → ℝ` be Gaussian processes (all finite-dimensional distributions Gaussian) under
probability measures `P` and `Q`. If the means agree, `P[X t] = Q[Y t]`, and the covariances agree,
`cov[X s, X t; P] = cov[Y s, Y t; Q]`, then the laws of `X` and `Y` on the product σ-algebra of `T → ℝ`
coincide.

Route: the finite-dimensional marginals are Gaussian on `ι → ℝ` (`HasGaussianLaw`), so their
characteristic functionals `charFunDual` are `exp (∫ L∘X - Var[L∘X] / 2)`; a continuous linear
functional on `ι → ℝ` is a linear combination of coordinates, so mean and variance of `L∘X` are fixed
by the means and covariances of the coordinates. The finite-dimensional laws then agree, and the
projective-limit uniqueness theorem identifies the two laws on the product σ-algebra. The joint map into
`T → ℝ` is assumed a.e. measurable; for countable `T` this follows from the coordinatewise a.e.
measurability that `IsGaussianProcess` provides.

Locator: standard (finite-dimensional distributions determine a law on the product σ-field, as in
Billingsley, *Probability and Measure*, §36; a Gaussian law is determined by its characteristic
functional, Bogachev, *Gaussian Measures*, §1.1 and §2.2). Theorem numbers to be confirmed.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-- A continuous linear functional on `ι → ℝ` is a linear combination of the coordinates. -/
lemma exists_strongDual_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) :
    ∃ c : ι → ℝ, ∀ x : ι → ℝ, L x = ∑ i, c i * x i := by
  refine ⟨fun i => L fun j => if i = j then 1 else 0, fun x => ?_⟩
  have h := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The mean of a linear combination of integrable variables. -/
lemma integral_sum_const_mul {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {X : ι → Ω → ℝ}
    {P : Measure Ω} [IsFiniteMeasure P] (hX : ∀ i, MemLp (X i) 2 P) (c : ι → ℝ) :
    ∫ ω, ∑ i, c i * X i ω ∂P = ∑ i, c i * ∫ ω, X i ω ∂P := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · intro i _
    exact ((hX i).integrable one_le_two).const_mul (c i)

/-- The variance of a linear combination of square-integrable variables is the bilinear form of the
covariances. -/
lemma variance_sum_const_mul {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {X : ι → Ω → ℝ}
    {P : Measure Ω} [IsFiniteMeasure P] (hX : ∀ i, MemLp (X i) 2 P) (c : ι → ℝ) :
    Var[fun ω ↦ ∑ i, c i * X i ω; P] = ∑ i, ∑ j, c i * c j * cov[X i, X j; P] := by
  have hXc : ∀ i, MemLp (fun ω ↦ c i * X i ω) 2 P := fun i => (hX i).const_mul (c i)
  have hm : AEMeasurable (fun ω ↦ ∑ i, c i * X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => ((hXc i).aemeasurable)
  rw [← covariance_self hm, covariance_fun_sum_fun_sum hXc hXc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Finite-dimensional version: a Gaussian vector is determined in law by its means and covariances. -/
theorem map_eq_of_mean_cov_fin {ι Ω Ω' : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : HasGaussianLaw (fun ω i ↦ X i ω) P) (hY : HasGaussianLaw (fun ω i ↦ Y i ω) Q)
    (hXi : ∀ i, MemLp (X i) 2 P) (hYi : ∀ i, MemLp (Y i) 2 Q)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = ∫ ω, Y i ω ∂Q)
    (hcov : ∀ i j, cov[X i, X j; P] = cov[Y i, Y j; Q]) :
    P.map (fun ω i ↦ X i ω) = Q.map (fun ω i ↦ Y i ω) := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  obtain ⟨c, hc⟩ := exists_strongDual_eq_sum L
  rw [hX.charFunDual_map_eq_fun, hY.charFunDual_map_eq_fun]
  have hXL : (fun ω ↦ L (fun i ↦ X i ω)) = fun ω ↦ ∑ i, c i * X i ω :=
    funext fun ω => hc _
  have hYL : (fun ω ↦ L (fun i ↦ Y i ω)) = fun ω ↦ ∑ i, c i * Y i ω :=
    funext fun ω => hc _
  rw [hXL, hYL, integral_sum_const_mul hXi c, integral_sum_const_mul hYi c,
    variance_sum_const_mul hXi c, variance_sum_const_mul hYi c]
  simp only [hmean, hcov]

/-- **Laws of Gaussian processes are determined by their means and covariances.** Let `X` and `Y` be
Gaussian processes indexed by `T` under probability measures `P` and `Q`, with equal means and equal
covariance functions, and if the joint maps `ω ↦ (X t ω)_t` and `ω ↦ (Y t ω)_t` are a.e. measurable into the
product σ-algebra of `T → ℝ` (automatic for countable `T`, see `gaussianProcess_map_eq_of_mean_cov_of_countable`),
then `X` and `Y` have the same law on the product σ-algebra of `T → ℝ`. -/
theorem gaussianProcess_map_eq_of_mean_cov {Ω Ω' T : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ} {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmean : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂Q)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q])
    (hF : AEMeasurable (fun ω t ↦ X t ω) P) (hG : AEMeasurable (fun ω t ↦ Y t ω) Q) :
    P.map (fun ω t ↦ X t ω) = Q.map (fun ω t ↦ Y t ω) := by
  classical
  -- equality of the finite-dimensional marginals
  have hfin : ∀ I : Finset T,
      P.map (fun ω (i : I) ↦ X i ω) = Q.map (fun ω (i : I) ↦ Y i ω) := fun I =>
    map_eq_of_mean_cov_fin (X := fun i : I ↦ X i) (Y := fun i : I ↦ Y i)
      (hX.hasGaussianLaw I) (hY.hasGaussianLaw I)
      (fun i => (hX.hasGaussianLaw_eval i).memLp_two)
      (fun i => (hY.hasGaussianLaw_eval i).memLp_two)
      (fun i => hmean i) (fun i j => hcov i j)
  -- both laws are projective limits of the same finite-dimensional family
  have hP : IsProjectiveLimit (P.map fun ω t ↦ X t ω)
      (fun I : Finset T => P.map fun ω (i : I) ↦ X i ω) := by
    intro I
    have hg : Measurable (I.restrict : (T → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : T)
    rw [hg.aemeasurable.map_map_of_aemeasurable hF]
    rfl
  have hQ : IsProjectiveLimit (Q.map fun ω t ↦ Y t ω)
      (fun I : Finset T => P.map fun ω (i : I) ↦ X i ω) := by
    intro I
    have hg : Measurable (I.restrict : (T → ℝ) → ∀ i : I, ℝ) :=
      Measurable.of_eval fun i => measurable_pi_apply (i : T)
    rw [hg.aemeasurable.map_map_of_aemeasurable hG]
    exact (hfin I).symm
  exact IsProjectiveLimit.unique hP hQ

/-- **The countable-index case.** If `T` is countable, the joint measurability hypotheses of
`gaussianProcess_map_eq_of_mean_cov` follow from the coordinatewise ones (`aemeasurable_pi_iff`). -/
theorem gaussianProcess_map_eq_of_mean_cov_of_countable {Ω Ω' T : Type*} [Countable T]
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmean : ∀ t, ∫ ω, X t ω ∂P = ∫ ω, Y t ω ∂Q)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q]) :
    P.map (fun ω t ↦ X t ω) = Q.map (fun ω t ↦ Y t ω) :=
  gaussianProcess_map_eq_of_mean_cov hX hY hmean hcov
    (aemeasurable_pi_iff.2 fun t => (hX.hasGaussianLaw_eval t).aemeasurable)
    (aemeasurable_pi_iff.2 fun t => (hY.hasGaussianLaw_eval t).aemeasurable)

end LatticeProb
