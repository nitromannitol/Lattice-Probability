/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianPredictableMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteStopping
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianQuadraticMoments

/-!
# Gaussian increment identities with actual past-measurable coefficients

These are the predictable linear and quadratic terms in the dyadic stopped
Taylor argument. Independence is derived from the full natural filtration,
not assumed for a random starting position or a rounded skeleton center.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma standardBrownianLaw_indepFun_shift_coefficient {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C) :
    IndepFun (shiftedBrownianPath t) C μ := by
  have hpast : Measurable[MeasurableSpace.comap
      (fun (ω : BrownianPath d) (s : Set.Iic t) ↦ ω s) inferInstance] C := by
    exact (brownianNaturalFiltration_eq_comap d t) ▸ hC
  apply (IndepFun_iff _ _ _).mpr
  intro S A hS hA
  exact (standardBrownianLaw_indepFun_shiftedPath hμ t).meas_inter hS
    (hpast.comap_le A hA)

/-- A coefficient known at time t has zero expectation against the next
Brownian increment, with the whole past retained. -/
theorem standardBrownianLaw_integral_predictable_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (i : Fin d) :
    (∫ ω, C ω * (ω (t + s) i - ω t i) ∂μ) = 0 := by
  have hmC : Measurable C := hC.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hmeval : Measurable (fun ω : BrownianPath d ↦ ω s i) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hmeval
  have hmean : (∫ ω, ω (t + s) i - ω t i ∂μ) = 0 :=
    ((hμ.2.1 i).shift t).integral_eval s
  exact (hind.integral_fun_mul_eq_mul_integral hmC.aestronglyMeasurable
    (hmeval.comp (measurable_shiftedBrownianPath t)).aestronglyMeasurable).trans
      (by
        change (∫ ω, C ω ∂μ) * (∫ ω, ω (t + s) i - ω t i ∂μ) = 0
        rw [hmean, mul_zero])

/-- The conditional covariance of the next actual increment is s times the
identity; the past coefficient may encode a stopping event and a Hessian entry. -/
theorem standardBrownianLaw_integral_predictable_quadratic {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    {C : BrownianPath d → ℝ} (hC : Measurable[brownianNaturalFiltration d t] C)
    (i j : Fin d) :
    (∫ ω, C ω * ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) ∂μ) =
      (∫ ω, C ω ∂μ) * (if i = j then (s : ℝ) else 0) := by
  have hmC : Measurable C := hC.mono ((brownianNaturalFiltration d).le t) le_rfl
  have hmquad : Measurable (fun ω : BrownianPath d ↦ ω s i * ω s j) :=
    (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i * ω s j)).measurable
  have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t hC).symm.comp
    measurable_id hmquad
  have hmoment : (∫ ω, (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j) ∂μ) =
      if i = j then (s : ℝ) else 0 := by
    have hm := standardBrownianLaw_integral_coordinate_mul
      (standardBrownianLaw_shift hμ t) s i j
    rw [integral_map (measurable_shiftedBrownianPath t).aemeasurable
      hmquad.aestronglyMeasurable] at hm
    exact hm
  exact (hind.integral_fun_mul_eq_mul_integral hmC.aestronglyMeasurable
    (hmquad.comp (measurable_shiftedBrownianPath t)).aestronglyMeasurable).trans
      (by
        change (∫ ω, C ω ∂μ) *
          (∫ ω, (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j) ∂μ) = _
        rw [hmoment])

/-- The full predictable quadratic term cancels when its actual coefficient
matrix has zero trace. Integrability of the coefficients is explicit; bounded
stopped Hessians supply it in the harmonic exit argument. -/
theorem standardBrownianLaw_integral_predictable_trace_zero {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hHint : ∀ i j, Integrable (H i j) μ)
    (htrace : ∀ ω, ∑ i, H i i ω = 0) :
    (∫ ω, ∑ i, ∑ j, H i j ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) ∂μ) = 0 := by
  have hincrement (i j : Fin d) : Integrable (fun ω : BrownianPath d ↦
      (ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) μ := by
    have htwo (k : Fin d) :
        MemLp (fun ω : BrownianPath d ↦ ω (t + s) k - ω t k) 2 μ :=
      ((hμ.2.1 k).hasLaw_sub (t + s) t).memLp (memLp_id_gaussianReal' 2 (by norm_num))
    exact (htwo i).integrable_mul (htwo j)
  have hint (i j : Fin d) : Integrable (fun ω : BrownianPath d ↦ H i j ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j))) μ := by
    have hmquad : Measurable (fun ω : BrownianPath d ↦ ω s i * ω s j) :=
      (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω s i * ω s j)).measurable
    have hind := (standardBrownianLaw_indepFun_shift_coefficient hμ t (hH i j)).symm.comp
      measurable_id hmquad
    exact hind.integrable_mul (hHint i j) (hincrement i j)
  calc
    _ = ∑ i, ∑ j, (∫ ω, H i j ω ∂μ) * (if i = j then (s : ℝ) else 0) := by
      rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hint i j))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum _ (fun j _ ↦ hint i j)]
      apply Finset.sum_congr rfl
      intro j hj
      exact standardBrownianLaw_integral_predictable_quadratic hμ t s (hH i j) i j
    _ = (s : ℝ) * ∑ i, ∫ ω, H i i ω ∂μ := by simp [mul_ite, Finset.mul_sum, mul_comm]
    _ = (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
      rw [integral_finset_sum _ (fun i _ ↦ hHint i i)]
    _ = 0 := by simp only [htrace, integral_zero, mul_zero]

end BouRabeeGwynne
