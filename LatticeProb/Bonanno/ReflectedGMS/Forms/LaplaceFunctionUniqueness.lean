/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.LaplaceFunctionUniqueness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.LaplaceMeasureUniqueness
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Uniqueness of functions from their Laplace transforms

Bounded nonnegative measurable functions on positive real times are equal
almost everywhere when all of their positive-parameter Laplace transforms
agree.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace ReflectedGMS

/-- Bounded nonnegative measurable functions on `(0, ∞)` are determined
almost everywhere by their Laplace transforms at positive parameters. -/
theorem ae_eq_of_integral_exp_neg_mul_eq
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hg_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ g t)
    (hf_le_one : ∀ t : ℝ, 0 < t → f t ≤ 1)
    (hg_le_one : ∀ t : ℝ, 0 < t → g t ≤ 1)
    (hlaplace : ∀ a : ℝ, 0 < a →
      (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * f t) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * g t) :
    f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
  let ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let wf : ℝ → ℝ := fun t => Real.exp (-t) * f t
  let wg : ℝ → ℝ := fun t => Real.exp (-t) * g t
  let μf : Measure ℝ := ρ.withDensity fun t => ENNReal.ofReal (wf t)
  let μg : Measure ℝ := ρ.withDensity fun t => ENNReal.ofReal (wg t)
  let νf : Measure ℝ≥0 := μf.map Real.toNNReal
  let νg : Measure ℝ≥0 := μg.map Real.toNNReal

  have hρf : HasFiniteIntegral wf ρ := by
    refine (exp_neg_integrableOn_Ioi 0 zero_lt_one).hasFiniteIntegral.mono' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf_nonneg t ht))]
    simpa only [neg_mul, one_mul] using
      mul_le_of_le_one_right (Real.exp_pos (-t)).le (hf_le_one t ht)
  have hρg : HasFiniteIntegral wg ρ := by
    refine (exp_neg_integrableOn_Ioi 0 zero_lt_one).hasFiniteIntegral.mono' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg_nonneg t ht))]
    simpa only [neg_mul, one_mul] using
      mul_le_of_le_one_right (Real.exp_pos (-t)).le (hg_le_one t ht)
  letI : IsFiniteMeasure μf := isFiniteMeasure_withDensity_ofReal hρf
  letI : IsFiniteMeasure μg := isFiniteMeasure_withDensity_ofReal hρg
  letI : IsFiniteMeasure νf := Measure.isFiniteMeasure_map μf Real.toNNReal
  letI : IsFiniteMeasure νg := Measure.isFiniteMeasure_map μg Real.toNNReal

  have hν : νf = νg := by
    apply measure_eq_of_integral_exp_neg_nat_mul_eq
    intro n
    rw [integral_map measurable_real_toNNReal.aemeasurable (by fun_prop)]
    rw [integral_map measurable_real_toNNReal.aemeasurable (by fun_prop)]
    rw [integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul]
    rw [show (∫ t, (ENNReal.ofReal (wf t)).toReal *
            Real.exp (-(n : ℝ) * (Real.toNNReal t : ℝ)) ∂ρ) =
          ∫ t in Ioi (0 : ℝ), Real.exp (-(n + 1 : ℝ) * t) * f t by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp only [Real.coe_toNNReal t ht.le, ENNReal.toReal_ofReal
          (mul_nonneg (Real.exp_pos _).le (hf_nonneg t ht)), wf]
        rw [show -(n + 1 : ℝ) * t = -(n : ℝ) * t + -t by ring, Real.exp_add]
        ring]
    rw [show (∫ t, (ENNReal.ofReal (wg t)).toReal *
            Real.exp (-(n : ℝ) * (Real.toNNReal t : ℝ)) ∂ρ) =
          ∫ t in Ioi (0 : ℝ), Real.exp (-(n + 1 : ℝ) * t) * g t by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp only [Real.coe_toNNReal t ht.le, ENNReal.toReal_ofReal
          (mul_nonneg (Real.exp_pos _).le (hg_nonneg t ht)), wg]
        rw [show -(n + 1 : ℝ) * t = -(n : ℝ) * t + -t by ring, Real.exp_add]
        ring]
    exact hlaplace (n + 1 : ℝ) (by positivity)

  have hμ : μf = μg := by
    have hback_f : μf.map (NNReal.toReal ∘ Real.toNNReal) = μf := by
      calc
        _ = μf.map id := Measure.map_congr <| by
          filter_upwards [withDensity_absolutelyContinuous ρ
              (fun t => ENNReal.ofReal (wf t)) (ae_restrict_mem measurableSet_Ioi)] with t ht
          exact Real.coe_toNNReal t ht.le
        _ = μf := by simp
    have hback_g : μg.map (NNReal.toReal ∘ Real.toNNReal) = μg := by
      calc
        _ = μg.map id := Measure.map_congr <| by
          filter_upwards [withDensity_absolutelyContinuous ρ
              (fun t => ENNReal.ofReal (wg t)) (ae_restrict_mem measurableSet_Ioi)] with t ht
          exact Real.coe_toNNReal t ht.le
        _ = μg := by simp
    calc
      μf = μf.map (NNReal.toReal ∘ Real.toNNReal) := hback_f.symm
      _ = νf.map (fun t : ℝ≥0 => (t : ℝ)) := by
        simpa only [νf] using
          (Measure.map_map (μ := μf) measurable_coe_nnreal_real measurable_real_toNNReal).symm
      _ = νg.map (fun t : ℝ≥0 => (t : ℝ)) := congrArg _ hν
      _ = μg.map (NNReal.toReal ∘ Real.toNNReal) := by
        simpa only [νg] using
          Measure.map_map (μ := μg) measurable_coe_nnreal_real measurable_real_toNNReal
      _ = μg := hback_g

  have hmf : Measurable fun t => ENNReal.ofReal (wf t) := by
    exact (measurable_id.neg.exp.mul hf).ennreal_ofReal
  have hmg : Measurable fun t => ENNReal.ofReal (wg t) := by
    exact (measurable_id.neg.exp.mul hg).ennreal_ofReal
  have hdensity : (fun t => ENNReal.ofReal (wf t)) =ᵐ[ρ]
      fun t => ENNReal.ofReal (wg t) := by
    exact (withDensity_eq_iff_of_sigmaFinite hmf.aemeasurable hmg.aemeasurable).mp hμ
  filter_upwards [hdensity, ae_restrict_mem measurableSet_Ioi] with t hden ht
  have hweight : wf t = wg t := by
    have hreal := congrArg ENNReal.toReal hden
    rw [ENNReal.toReal_ofReal
        (mul_nonneg (Real.exp_pos _).le (hf_nonneg t ht)),
      ENNReal.toReal_ofReal
        (mul_nonneg (Real.exp_pos _).le (hg_nonneg t ht))] at hreal
    exact hreal
  exact mul_left_cancel₀ (Real.exp_ne_zero (-t)) hweight

end ReflectedGMS
