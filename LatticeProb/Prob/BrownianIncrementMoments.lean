/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianQuadraticMoments.lean.
-/

import LatticeProb.Prob.BrownianPathSpace
import LatticeProb.Prob.BrownianMomentsCore
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance

/-!
# Second and fourth moments of standard Brownian increments

For a standard Brownian law on paths `ℝ≥0 → Euc d`, the coordinates of the path at a fixed time
`t` are independent centred Gaussians with variance `t`. This file derives the exact second
moments of the coordinate products, the trace identity for a quadratic form in the coordinates
at time `t`, and a dimension-explicit bound on the fourth moment of the Euclidean norm.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- A random variable with centred Gaussian law of variance `v` is in `L²`. -/
private lemma memLp_two_of_hasLaw_gaussian {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    {X : Ω' → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : MemLp X 2 μ := by
  have h : MemLp id (2 : ℝ≥0∞) (gaussianReal 0 v) := memLp_id_gaussianReal' _ (by norm_num)
  rw [← hX.map_eq] at h
  exact (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).mp h

/-- The fourth power of a random variable with centred Gaussian law of variance `v` is
integrable. -/
private lemma integrable_fourth_of_hasLaw_gaussian {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω'} {X : Ω' → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) :
    Integrable (fun ω ↦ X ω ^ 4) μ := by
  have h := gaussianReal_integrable_fourth_power v
  rw [← hX.map_eq] at h
  exact (integrable_map_measure (continuous_pow 4).aestronglyMeasurable hX.aemeasurable).mp h

/-- Products of two coordinates of a standard Brownian path at a fixed time are integrable. -/
lemma standardBrownianLaw_integrable_coordinate_mul {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (i j : Fin d) :
    Integrable (fun ω ↦ ω t i * ω t j) μ := by
  have htwo (k : Fin d) : MemLp (fun ω : BrownianPath d ↦ ω t k) 2 μ :=
    memLp_two_of_hasLaw_gaussian ((hμ.2.1 k).hasLaw_eval t)
  exact (htwo i).integrable_mul (htwo j)

/-- The actual covariance matrix at time t is t times the identity. -/
theorem standardBrownianLaw_integral_coordinate_mul {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (i j : Fin d) :
    (∫ ω, ω t i * ω t j ∂μ) = if i = j then (t : ℝ) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa only [covariance, (hμ.2.1 i).integral_eval, sub_zero, min_self, ite_true] using
      (hμ.2.1 i).covariance_eval t t
  · have hind : IndepFun (fun ω : BrownianPath d ↦ ω t i)
        (fun ω : BrownianPath d ↦ ω t j) μ :=
      (hμ.2.2.indepFun hij).comp (measurable_pi_apply t) (measurable_pi_apply t)
    rw [if_neg hij, hind.integral_fun_mul_eq_mul_integral
      ((hμ.2.1 i).integrable_eval t).aestronglyMeasurable
      ((hμ.2.1 j).integrable_eval t).aestronglyMeasurable,
      (hμ.2.1 i).integral_eval, zero_mul]

/-- Integrating a quadratic form in the coordinates of a standard Brownian path at time `t`
gives exactly `t` times the trace of the form, with no isotropy assumption supplied
separately. -/
theorem standardBrownianLaw_integral_quadratic {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (H : Fin d → Fin d → ℝ) :
    (∫ ω, ∑ i, ∑ j, H i j * (ω t i * ω t j) ∂μ) =
      (t : ℝ) * ∑ i, H i i := by
  have hint (i j : Fin d) :
      Integrable (fun ω : BrownianPath d ↦ H i j * (ω t i * ω t j)) μ :=
    (standardBrownianLaw_integrable_coordinate_mul hμ t i j).const_mul _
  have hrow (i : Fin d) :
      Integrable (fun ω : BrownianPath d ↦ ∑ j, H i j * (ω t i * ω t j)) μ :=
    integrable_finsetSum _ (fun j _ ↦ hint i j)
  rw [integral_finsetSum _ (fun i _ ↦ hrow i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
  simp only [integral_const_mul, standardBrownianLaw_integral_coordinate_mul hμ]
  simp [mul_ite, mul_comm]

/-- The fourth power of the Euclidean norm of a vector in `Euc d` is at most `d` times the sum of
the fourth powers of its coordinates. -/
lemma euclidean_norm_fourth_le_coordinate_fourth {d : ℕ} (x : Euc d) :
    ‖x‖ ^ 4 ≤ (d : ℝ) * ∑ i, x i ^ 4 := by
  calc
    ‖x‖ ^ 4 = (∑ i, x i ^ 2) ^ 2 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      ring
    _ ≤ (d : ℝ) * ∑ i, (x i ^ 2) ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ x i ^ 2))
    _ = (d : ℝ) * ∑ i, x i ^ 4 := by norm_num [← pow_mul]

/-- The fourth power of the Euclidean norm of a standard Brownian path at a fixed time is
integrable. -/
lemma standardBrownianLaw_integrable_norm_fourth {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ ‖ω t‖ ^ 4) μ := by
  have hi (i : Fin d) : Integrable (fun ω : BrownianPath d ↦ ω t i ^ 4) μ :=
    integrable_fourth_of_hasLaw_gaussian ((hμ.2.1 i).hasLaw_eval t)
  have hbound : Integrable (fun ω : BrownianPath d ↦ (d : ℝ) * ∑ i, ω t i ^ 4) μ :=
    (integrable_finsetSum _ (fun i _ ↦ hi i)).const_mul _
  have hm : AEStronglyMeasurable (fun ω : BrownianPath d ↦ ‖ω t‖ ^ 4) μ :=
    ((continuous_eval_const t).norm.pow 4).aestronglyMeasurable
  apply hbound.mono' hm
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖ω t‖ ^ 4)]
  exact euclidean_norm_fourth_le_coordinate_fourth (ω t)

/-- Dimension-explicit bound on the fourth moment of the Euclidean norm of a standard Brownian
path at a fixed time: it is at most `3 d² t²`. -/
theorem standardBrownianLaw_integral_norm_fourth_le {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    (∫ ω, ‖ω t‖ ^ 4 ∂μ) ≤ 3 * (d : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
  have hi (i : Fin d) : Integrable (fun ω : BrownianPath d ↦ ω t i ^ 4) μ :=
    integrable_fourth_of_hasLaw_gaussian ((hμ.2.1 i).hasLaw_eval t)
  calc
    (∫ ω, ‖ω t‖ ^ 4 ∂μ) ≤ ∫ ω, (d : ℝ) * ∑ i, ω t i ^ 4 ∂μ :=
      integral_mono (standardBrownianLaw_integrable_norm_fourth hμ t)
        ((integrable_finsetSum _ (fun i _ ↦ hi i)).const_mul _)
        (fun ω ↦ euclidean_norm_fourth_le_coordinate_fourth (ω t))
    _ = (d : ℝ) * ∑ i : Fin d, 3 * (t : ℝ) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      calc
        (∫ ω, ω t i ^ 4 ∂μ) = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 t :=
          ((hμ.2.1 i).hasLaw_eval t).integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
        _ = _ := gaussianReal_fourth_moment t
    _ = _ := by simp; ring

namespace BrownianIncrementMomentsExample

/-- The quadratic identity for the explicit form `[[1, 2], [3, 4]]`, for any standard Brownian
law `μ` on two-dimensional paths: the integral is `5 t`, the trace times `t`. -/
theorem standardBrownianLaw_integral_quadratic_example {μ : Measure (BrownianPath 2)}
    (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    (∫ ω, ∑ i, ∑ j, (![![1, 2], ![3, 4]] : Fin 2 → Fin 2 → ℝ) i j * (ω t i * ω t j) ∂μ) =
      (t : ℝ) * 5 := by
  rw [standardBrownianLaw_integral_quadratic hμ]
  norm_num [Fin.sum_univ_two]

/-- The fourth-moment comparison at the concrete vector `(1, 2)` of `Euc 2`: its norm to the
fourth power is at most `2 (1⁴ + 2⁴) = 34`. -/
theorem euclidean_norm_fourth_le_example :
    ‖(!₂[1, 2] : Euc 2)‖ ^ 4 ≤ 34 :=
  (euclidean_norm_fourth_le_coordinate_fourth _).trans (by norm_num [Fin.sum_univ_two])

end BrownianIncrementMomentsExample

end LatticeProb
