module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
# Characteristic-function limits

Convergence of the characteristic functions `t ↦ E[exp (i t S n)]` to `exp (-v t² / 2)` for every
`t` implies convergence in distribution to `gaussianReal 0 v`, by Lévy's continuity theorem. The
file also records that changing the random variables on a set of small probability changes the
characteristic functions by a small amount, which transfers the limit to a sequence that differs
from the original one only on such a set.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace LatticeProb.McLeish

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- If the characteristic functions `t ↦ E[exp (i t S n)]` converge pointwise to those of the
centred Gaussian law with variance `v`, then `S n` converges in distribution to `gaussianReal 0 v`. -/
theorem tendstoInDistribution_gaussianReal_of_tendsto_integral_exp
    (S : ℕ → Ω → ℝ) (hS : ∀ n, AEMeasurable (S n) P) (v : ℝ≥0)
    (h : ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((t * S n ω : ℝ) : ℂ)) ∂P) atTop
      (𝓝 (Complex.exp ((-((v : ℝ) * t ^ 2 / 2) : ℝ) : ℂ)))) :
    TendstoInDistribution S atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 v) where
  forall_aemeasurable := hS
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    have hlim : charFun ((gaussianReal 0 v).map id) t =
        Complex.exp ((-((v : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) := by
      rw [Measure.map_id, charFun_gaussianReal]
      congr 1
      push_cast
      ring
    have hmap : ∀ n, charFun (P.map (S n)) t =
        ∫ ω, Complex.exp (Complex.I * ((t * S n ω : ℝ) : ℂ)) ∂P := by
      intro n
      rw [charFun_apply_real, integral_map (hS n)
        (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x : ℝ =>
          Complex.exp (t * x * Complex.I)))]
      congr 1
      funext ω
      congr 1
      push_cast
      ring
    show Tendsto (fun n => charFun (P.map (S n)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 v).map id) t))
    rw [hlim]
    exact Tendsto.congr (fun n => (hmap n).symm) (h t)

/-- Replacing `S` by `S'` changes the characteristic function `t ↦ E[exp (i t S)]` by at most
`2 * P {S ≠ S'}`. -/
theorem norm_integral_exp_sub_integral_exp_le
    (S S' : Ω → ℝ) (hS : Measurable S) (hS' : Measurable S') (t : ℝ) :
    ‖∫ ω, Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) ∂P -
        ∫ ω, Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ)) ∂P‖ ≤ 2 * P.real {ω | S ω ≠ S' ω} := by
  have hset : MeasurableSet {ω | S ω ≠ S' ω} := (measurableSet_eq_fun hS hS').compl
  have hfm : Measurable fun ω => Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) := by fun_prop
  have hgm : Measurable fun ω => Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ)) := by fun_prop
  have hfi : Integrable (fun ω => Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ))) P :=
    Integrable.of_bound (C := 1) hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hgi : Integrable (fun ω => Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))) P :=
    Integrable.of_bound (C := 1) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hdiff : Integrable (fun ω => ‖Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))‖) P := (hfi.sub hgi).norm
  have hbound : Integrable (fun ω => 2 * Set.indicator {ω | S ω ≠ S' ω} (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hset).const_mul 2
  have hpt : ∀ ω, ‖Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))‖ ≤
      2 * Set.indicator {ω | S ω ≠ S' ω} (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : S ω = S' ω
    · have hω' : ω ∉ {ω | S ω ≠ S' ω} := fun h => h hω
      rw [Set.indicator_of_notMem hω', hω, sub_self, norm_zero, mul_zero]
    · rw [Set.indicator_of_mem (show ω ∈ {ω | S ω ≠ S' ω} from hω), mul_one]
      calc _ ≤ ‖Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ))‖ +
            ‖Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num
  have hsub : ∫ ω, (Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))) ∂P =
      ∫ ω, Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) ∂P -
        ∫ ω, Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ)) ∂P :=
    integral_sub hfi hgi
  calc ‖∫ ω, Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) ∂P -
        ∫ ω, Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ)) ∂P‖
      = ‖∫ ω, (Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))) ∂P‖ := by rw [hsub]
    _ ≤ ∫ ω, ‖Complex.exp (Complex.I * ((t * S ω : ℝ) : ℂ)) -
          Complex.exp (Complex.I * ((t * S' ω : ℝ) : ℂ))‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 2 * Set.indicator {ω | S ω ≠ S' ω} (fun _ => (1 : ℝ)) ω ∂P :=
        integral_mono hdiff hbound hpt
    _ = 2 * ∫ ω, Set.indicator {ω | S ω ≠ S' ω} (fun _ => (1 : ℝ)) ω ∂P :=
        integral_const_mul _ _
    _ = 2 * P.real {ω | S ω ≠ S' ω} := by
        rw [integral_indicator_const _ hset, smul_eq_mul, mul_one]

/-- If the sequences `S n` and `S' n` differ on sets whose probabilities tend to zero, and the
characteristic functions of `S' n` at `t` converge to `a`, then so do those of `S n`. -/
theorem tendsto_integral_exp_of_tendsto_measure_ne
    (S S' : ℕ → Ω → ℝ) (hS : ∀ n, Measurable (S n)) (hS' : ∀ n, Measurable (S' n)) (t : ℝ) (a : ℂ)
    (hne : Tendsto (fun n => P {ω | S n ω ≠ S' n ω}) atTop (𝓝 0))
    (h' : Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((t * S' n ω : ℝ) : ℂ)) ∂P) atTop (𝓝 a)) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((t * S n ω : ℝ) : ℂ)) ∂P) atTop (𝓝 a) := by
  have hr : Tendsto (fun n => P.real {ω | S n ω ≠ S' n ω}) atTop (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hne
    rw [ENNReal.toReal_zero] at h0
    exact h0
  have hd : Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((t * S n ω : ℝ) : ℂ)) ∂P -
      ∫ ω, Complex.exp (Complex.I * ((t * S' n ω : ℝ) : ℂ)) ∂P) atTop (𝓝 0) := by
    have h2 := hr.const_mul 2
    rw [mul_zero] at h2
    exact squeeze_zero_norm (fun n => norm_integral_exp_sub_integral_exp_le (S n) (S' n)
      (hS n) (hS' n) t) h2
  have := hd.add h'
  simp only [sub_add_cancel, zero_add] at this
  exact this

end LatticeProb.McLeish
