/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianQuadraticMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import LatticeProb.Bonanno.BouRabeeGwynne.GaussianIncrementBounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance

/-!
# The exact Gaussian quadratic generator term

These identities use the actual standard Brownian coordinate laws and whole
coordinate independence. They identify the quadratic Taylor term with the
trace, which is the analytic input to harmonic exit representation in every
dimension.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma standardBrownianLaw_integrable_coordinate_mul {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (i j : Fin d) :
    Integrable (fun ω ↦ ω t i * ω t j) μ := by
  have htwo (k : Fin d) : MemLp (fun ω : BrownianPath d ↦ ω t k) 2 μ :=
    ((hμ.2.1 k).hasLaw_eval t).memLp (memLp_id_gaussianReal' 2 (by norm_num))
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

/-- Integrating the actual quadratic Taylor polynomial gives exactly its
coefficient trace times t, with no isotropy assumption supplied separately. -/
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
    integrable_finset_sum _ (fun j _ ↦ hint i j)
  rw [integral_finset_sum _ (fun i _ ↦ hrow i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ ↦ hint i j)]
  simp only [integral_const_mul, standardBrownianLaw_integral_coordinate_mul hμ]
  simp [mul_ite, mul_comm]

lemma euclidean_norm_fourth_le_coordinate_fourth {d : ℕ} (x : Euc d) :
    ‖x‖ ^ 4 ≤ (d : ℝ) * ∑ i, x i ^ 4 := by
  calc
    ‖x‖ ^ 4 = (∑ i, x i ^ 2) ^ 2 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      ring
    _ ≤ (d : ℝ) * ∑ i, (x i ^ 2) ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ x i ^ 2))
    _ = (d : ℝ) * ∑ i, x i ^ 4 := by norm_num [← pow_mul]

lemma standardBrownianLaw_integrable_norm_fourth {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ ‖ω t‖ ^ 4) μ := by
  have hi (i : Fin d) : Integrable (fun ω : BrownianPath d ↦ ω t i ^ 4) μ :=
    ((hμ.2.1 i).hasLaw_eval t).integrable_fun_comp (gaussianReal_integrable_fourth_power t)
  have hbound : Integrable (fun ω : BrownianPath d ↦ (d : ℝ) * ∑ i, ω t i ^ 4) μ :=
    (integrable_finset_sum _ (fun i _ ↦ hi i)).const_mul _
  have hm : AEStronglyMeasurable (fun ω : BrownianPath d ↦ ‖ω t‖ ^ 4) μ :=
    ((continuous_eval_const t).norm.pow 4).aestronglyMeasurable
  apply hbound.mono' hm
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖ω t‖ ^ 4)]
  exact euclidean_norm_fourth_le_coordinate_fourth (ω t)

/-- Dimension-explicit fourth moment used to bound the large Gaussian jumps
in the stopped Taylor expansion. -/
theorem standardBrownianLaw_integral_norm_fourth_le {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    (∫ ω, ‖ω t‖ ^ 4 ∂μ) ≤ 3 * (d : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
  have hi (i : Fin d) : Integrable (fun ω : BrownianPath d ↦ ω t i ^ 4) μ :=
    ((hμ.2.1 i).hasLaw_eval t).integrable_fun_comp (gaussianReal_integrable_fourth_power t)
  calc
    (∫ ω, ‖ω t‖ ^ 4 ∂μ) ≤ ∫ ω, (d : ℝ) * ∑ i, ω t i ^ 4 ∂μ :=
      integral_mono (standardBrownianLaw_integrable_norm_fourth hμ t)
        ((integrable_finset_sum _ (fun i _ ↦ hi i)).const_mul _)
        (fun ω ↦ euclidean_norm_fourth_le_coordinate_fourth (ω t))
    _ = (d : ℝ) * ∑ i : Fin d, 3 * (t : ℝ) ^ 2 := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ ↦ hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      calc
        (∫ ω, ω t i ^ 4 ∂μ) = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 t :=
          ((hμ.2.1 i).hasLaw_eval t).integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
        _ = _ := gaussianReal_fourth_moment t
    _ = _ := by simp; ring

end BouRabeeGwynne
