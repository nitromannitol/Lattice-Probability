/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ExponentialHoldingMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Existence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Mean and second moment of the unit exponential holding law

Manuscript consumer: `p:thm:exactclt` (`reflected_gms_ae_lines.tex:1655`), whose proof
replaces every actual holding interval of the reflected walk by its exact mean length and
needs the resulting compensated defect to be negligible after diffusive rescaling.  In the
Lean development that step is
`ReflectedGMS.ExactClockFluctuationControl.clockDefect h E N = ∑_{k<N} h k * (1 - E k)`
and `ExactClockFluctuationControl.abs_visitClock_sub_le`, whose bound `D` is a bound on the
compensated defect: controlling it in `L²` needs exactly the first two moments of a single
unit exponential holding variable, namely `𝔼[E] = 1` and `𝔼[(1 - E)²] = 1`.

The law in question is the one actually used by the construction: each unit holding time of
`ReflectedWalk.Existence` is a coordinate of the i.i.d. family
`ReflectedWalk.expFamily = Measure.infinitePi (fun _ => expMeasure 1)`
(`ReflectedWalk/RateFunction.lean`), so each coordinate has law `expMeasure 1`
(`ReflectedWalk.Existence.expFamily_map_eval`).

**Library gap.**  `Mathlib/Probability/Distributions/Exponential.lean` provides the density
and the CDF of `expMeasure r` but no mean and no variance, and `Gamma.lean` has none either.
The nearest existing repository result is
`ReflectedGMS.Temporal.ReflectedCycleOccupationProducer.lintegral_expMeasure_id`, which
computes the mean of `expMeasure r` as a *lower* Lebesgue integral in `ℝ≥0∞`.  That form is
not usable here: the consumer's defect `∑ h k * (1 - E k)` is a signed real quantity, so the
Bochner integral and the corresponding `Integrable` statements are required.  This file
supplies the missing Bochner-integral computation, through the same Gamma-integral route
(`Real.integral_rpow_mul_exp_neg_mul_Ioi` with `Real.Gamma 2 = 1` and `Real.Gamma 3 = 2`,
which is shorter than going through `Real.Gamma_eq_integral`), and states the results both
for `expMeasure 1` and for a single coordinate of `ReflectedWalk.expFamily`.

## Main results

* `integral_expMeasure_one`, `integrable_expMeasure_one_iff` — expectation under the unit
  exponential law as a weighted integral over `(0, ∞)` with weight `e^{-t}`;
* `integral_id_expMeasure_one : ∫ t, t ∂expMeasure 1 = 1` (the mean);
* `integral_sq_expMeasure_one : ∫ t, t ^ 2 ∂expMeasure 1 = 2` (the second moment);
* `integral_one_sub_sq_expMeasure_one : ∫ t, (1 - t) ^ 2 ∂expMeasure 1 = 1` (the variance,
  in the centred form the clock defect uses);
* `integral_eval_expFamily`, `integral_sq_eval_expFamily`, `integral_one_sub_eval_expFamily`,
  `integral_one_sub_eval_sq_expFamily` — the same four statements for the coordinate
  `e ↦ e a` of the actual i.i.d. family, together with their `Integrable` counterparts.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set

namespace ReflectedGMS.Process.ExponentialHoldingMoments

/-! ### The unit exponential density as the weight `e^{-t}` on `[0, ∞)` -/

/-- The unit exponential density, as a real number, is `e^{-t}` on `[0, ∞)` and `0` elsewhere. -/
theorem toReal_exponentialPDF_one (t : ℝ) :
    (exponentialPDF 1 t).toReal
      = Set.indicator (Set.Ici (0 : ℝ)) (fun s => Real.exp (-s)) t := by
  rcases le_or_gt 0 t with ht | ht
  · rw [exponentialPDF_of_nonneg ht, Set.indicator_of_mem (Set.mem_Ici.mpr ht)]
    simp only [one_mul]
    exact ENNReal.toReal_ofReal (Real.exp_nonneg _)
  · rw [exponentialPDF_of_neg ht, Set.indicator_of_notMem (by simpa using ht)]
    simp

/-- The unit exponential density is measurable. -/
theorem measurable_exponentialPDF_one : Measurable (exponentialPDF 1) :=
  (measurable_exponentialPDFReal 1).ennreal_ofReal

/-- The unit exponential density is finite everywhere. -/
theorem exponentialPDF_one_lt_top :
    ∀ᵐ t ∂(volume : Measure ℝ), exponentialPDF 1 t < ⊤ := by
  filter_upwards with t
  exact ENNReal.ofReal_lt_top

/-- Weighting a real function by the unit exponential density is restriction to `[0, ∞)`
against `e^{-t}`. -/
theorem smul_toReal_exponentialPDF_one (g : ℝ → ℝ) (t : ℝ) :
    (exponentialPDF 1 t).toReal • g t
      = Set.indicator (Set.Ici (0 : ℝ)) (fun s => Real.exp (-s) * g s) t := by
  rw [smul_eq_mul, toReal_exponentialPDF_one]
  by_cases ht : (0 : ℝ) ≤ t
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr ht), Set.indicator_of_mem (Set.mem_Ici.mpr ht)]
  · rw [Set.indicator_of_notMem (by simpa using ht),
      Set.indicator_of_notMem (by simpa using ht), zero_mul]

/-- Expectations under the unit exponential law are `e^{-t}`-weighted integrals over
`(0, ∞)`. -/
theorem integral_expMeasure_one (g : ℝ → ℝ) :
    ∫ t, g t ∂(expMeasure 1) = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * g t := by
  have hdens : expMeasure 1 = (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  rw [hdens, integral_withDensity_eq_integral_toReal_smul measurable_exponentialPDF_one
    exponentialPDF_one_lt_top]
  simp_rw [smul_toReal_exponentialPDF_one g]
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- Integrability under the unit exponential law is `e^{-t}`-weighted integrability over
`(0, ∞)`. -/
theorem integrable_expMeasure_one_iff (g : ℝ → ℝ) :
    Integrable g (expMeasure 1)
      ↔ IntegrableOn (fun t : ℝ => Real.exp (-t) * g t) (Set.Ioi 0) := by
  have hdens : expMeasure 1 = (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  rw [hdens, integrable_withDensity_iff_integrable_smul' measurable_exponentialPDF_one
    exponentialPDF_one_lt_top]
  simp_rw [smul_toReal_exponentialPDF_one g]
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]

/-! ### The two Gamma integrals -/

/-- `Γ(2) = 1`. -/
theorem Gamma_two_eq_one : Real.Gamma 2 = 1 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one]

/-- `Γ(3) = 2`. -/
theorem Gamma_three_eq_two : Real.Gamma 3 = 2 := by
  rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num : (2 : ℝ) ≠ 0),
    Gamma_two_eq_one, mul_one]

/-- `t ↦ e^{-t} t^n` is integrable on `(0, ∞)` for every `n`. -/
theorem integrableOn_exp_neg_mul_pow (n : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := 1)
    hs one_pos one_pos
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul, one_mul]
  ring

/-- `∫_0^∞ e^{-t} t dt = Γ(2) = 1`. -/
theorem integral_Ioi_exp_neg_mul_self :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) two_pos one_pos
  have hrhs : ((1 : ℝ) / 1) ^ (2 : ℝ) * Real.Gamma 2 = 1 := by
    rw [one_div_one, Real.one_rpow, one_mul, Gamma_two_eq_one]
  rw [hrhs] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul]
  ring

/-- `∫_0^∞ e^{-t} t² dt = Γ(3) = 2`. -/
theorem integral_Ioi_exp_neg_mul_sq :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ 2 = 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1) (by norm_num) one_pos
  have hrhs : ((1 : ℝ) / 1) ^ (3 : ℝ) * Real.Gamma 3 = 2 := by
    rw [one_div_one, Real.one_rpow, one_mul, Gamma_three_eq_two]
  rw [hrhs] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_mul]
  ring

/-! ### The first two moments of the unit exponential law -/

/-- A unit exponential holding variable is integrable. -/
theorem integrable_id_expMeasure_one : Integrable (fun t : ℝ => t) (expMeasure 1) := by
  have h := integrableOn_exp_neg_mul_pow 1
  simp only [pow_one] at h
  rw [integrable_expMeasure_one_iff]
  exact h

/-- A unit exponential holding variable is square integrable. -/
theorem integrable_sq_expMeasure_one : Integrable (fun t : ℝ => t ^ 2) (expMeasure 1) :=
  (integrable_expMeasure_one_iff (fun t : ℝ => t ^ 2)).mpr (integrableOn_exp_neg_mul_pow 2)

/-- **The mean of the unit exponential holding law is `1`.** -/
theorem integral_id_expMeasure_one : ∫ t, t ∂(expMeasure 1) = 1 :=
  (integral_expMeasure_one (fun t : ℝ => t)).trans integral_Ioi_exp_neg_mul_self

/-- **The second moment of the unit exponential holding law is `2`.** -/
theorem integral_sq_expMeasure_one : ∫ t, t ^ 2 ∂(expMeasure 1) = 2 :=
  (integral_expMeasure_one (fun t : ℝ => t ^ 2)).trans integral_Ioi_exp_neg_mul_sq

/-- The centred square `(1 - t)²` is integrable under the unit exponential law. -/
theorem integrable_one_sub_sq_expMeasure_one :
    Integrable (fun t : ℝ => (1 - t) ^ 2) (expMeasure 1) := by
  have h : (fun t : ℝ => (1 - t) ^ 2) = fun t : ℝ => 1 - 2 * t + t ^ 2 := by
    funext t; ring
  rw [h]
  exact ((integrable_const (1 : ℝ)).sub (integrable_id_expMeasure_one.const_mul 2)).add
    integrable_sq_expMeasure_one

/-- **The compensated second moment of the unit exponential holding law is `1`**:
`𝔼[(1 - E)²] = 1`.  This is the per-visit variance entering the bound `D` on
`ExactClockFluctuationControl.clockDefect`. -/
theorem integral_one_sub_sq_expMeasure_one :
    ∫ t, (1 - t) ^ 2 ∂(expMeasure 1) = 1 := by
  have hexp : ∀ t : ℝ, (1 - t) ^ 2 = 1 - 2 * t + t ^ 2 := fun t => by ring
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (expMeasure 1) := integrable_const 1
  have hlin : Integrable (fun t : ℝ => 2 * t) (expMeasure 1) :=
    integrable_id_expMeasure_one.const_mul 2
  have hone : ∫ _t : ℝ, (1 : ℝ) ∂(expMeasure 1) = 1 := by simp
  have hlinval : ∫ t : ℝ, 2 * t ∂(expMeasure 1) = 2 := by
    rw [integral_const_mul, integral_id_expMeasure_one, mul_one]
  calc ∫ t, (1 - t) ^ 2 ∂(expMeasure 1)
      = ∫ t, (1 - 2 * t + t ^ 2) ∂(expMeasure 1) := by simp_rw [hexp]
    _ = ∫ t, (1 - 2 * t) ∂(expMeasure 1) + ∫ t, t ^ 2 ∂(expMeasure 1) :=
        integral_add (hconst.sub hlin) integrable_sq_expMeasure_one
    _ = (∫ _t : ℝ, (1 : ℝ) ∂(expMeasure 1) - ∫ t : ℝ, 2 * t ∂(expMeasure 1))
          + ∫ t, t ^ 2 ∂(expMeasure 1) := by rw [integral_sub hconst hlin]
    _ = 1 := by rw [hone, hlinval, integral_sq_expMeasure_one]; norm_num

/-! ### The same moments for one coordinate of the actual i.i.d. holding family -/

/-- A functional of a single unit holding time of `ReflectedWalk.Existence` has the same
expectation as under `expMeasure 1`. -/
theorem integral_comp_eval_expFamily {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (expMeasure 1)) (a : ℕ →₀ ℕ) :
    ∫ e, g (e a) ∂ReflectedWalk.expFamily = ∫ t, g t ∂(expMeasure 1) := by
  have hmap : ReflectedWalk.expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => e a) = expMeasure 1 :=
    ReflectedWalk.Existence.expFamily_map_eval a
  have hg' : AEStronglyMeasurable g
      (ReflectedWalk.expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => e a)) := by
    rw [hmap]; exact hg
  have h := integral_map (μ := ReflectedWalk.expFamily)
    (φ := fun e : (ℕ →₀ ℕ) → ℝ => e a) (measurable_pi_apply a).aemeasurable hg'
  rw [hmap] at h
  exact h.symm

/-- A functional of a single unit holding time of `ReflectedWalk.Existence` is integrable as
soon as it is integrable under `expMeasure 1`. -/
theorem integrable_comp_eval_expFamily {g : ℝ → ℝ}
    (hg : Integrable g (expMeasure 1)) (a : ℕ →₀ ℕ) :
    Integrable (fun e : (ℕ →₀ ℕ) → ℝ => g (e a)) ReflectedWalk.expFamily := by
  have hmap : ReflectedWalk.expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => e a) = expMeasure 1 :=
    ReflectedWalk.Existence.expFamily_map_eval a
  have hg' : Integrable g (ReflectedWalk.expFamily.map (fun e : (ℕ →₀ ℕ) → ℝ => e a)) := by
    rw [hmap]; exact hg
  have h := (integrable_map_measure hg'.aestronglyMeasurable
    (measurable_pi_apply a).aemeasurable).mp hg'
  simpa [Function.comp_def] using h

/-- Each unit holding time of the actual construction is integrable. -/
theorem integrable_eval_expFamily (a : ℕ →₀ ℕ) :
    Integrable (fun e : (ℕ →₀ ℕ) → ℝ => e a) ReflectedWalk.expFamily :=
  integrable_comp_eval_expFamily (g := fun t : ℝ => t) integrable_id_expMeasure_one a

/-- The compensated unit holding time is square integrable. -/
theorem integrable_one_sub_eval_sq_expFamily (a : ℕ →₀ ℕ) :
    Integrable (fun e : (ℕ →₀ ℕ) → ℝ => (1 - e a) ^ 2) ReflectedWalk.expFamily :=
  integrable_comp_eval_expFamily (g := fun t : ℝ => (1 - t) ^ 2)
    integrable_one_sub_sq_expMeasure_one a

/-- **`𝔼[E_a] = 1`** for each unit holding time of `ReflectedWalk.Existence`. -/
theorem integral_eval_expFamily (a : ℕ →₀ ℕ) :
    ∫ e, e a ∂ReflectedWalk.expFamily = 1 :=
  (integral_comp_eval_expFamily (g := fun t : ℝ => t)
    measurable_id.aestronglyMeasurable a).trans integral_id_expMeasure_one

/-- **The compensated unit holding time is centred**, `𝔼[1 - E_a] = 0`: each complete visit
contributes a mean-zero defect to `ExactClockFluctuationControl.clockDefect`. -/
theorem integral_one_sub_eval_expFamily (a : ℕ →₀ ℕ) :
    ∫ e, (1 - e a) ∂ReflectedWalk.expFamily = 0 := by
  have : IsProbabilityMeasure ReflectedWalk.expFamily :=
    ReflectedWalk.expFamily_isProbabilityMeasure
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_eval_expFamily a),
    integral_eval_expFamily a]
  simp

/-- **`𝔼[(1 - E_a)²] = 1`** for each unit holding time of `ReflectedWalk.Existence`.
Together with `integral_one_sub_eval_expFamily` this is the exact per-visit input for the
bound `D` of `ExactClockFluctuationControl.abs_visitClock_sub_le`. -/
theorem integral_one_sub_eval_sq_expFamily (a : ℕ →₀ ℕ) :
    ∫ e, (1 - e a) ^ 2 ∂ReflectedWalk.expFamily = 1 :=
  (integral_comp_eval_expFamily (g := fun t : ℝ => (1 - t) ^ 2)
    (((continuous_const.sub continuous_id).pow 2).aestronglyMeasurable) a).trans
    integral_one_sub_sq_expMeasure_one

end ReflectedGMS.Process.ExponentialHoldingMoments
