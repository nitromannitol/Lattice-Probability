/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TraceDiscountedOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceRenewal
import LatticeProb.Bonanno.ReflectedGMS.Forms.DiscountedTraceStep
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Discounted occupation of the finite induced chain

This file starts the probabilistic identification left open by
`FiniteTraceRenewal`.  It uses the existing joint law
`MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w`; no new process or Markov
hypothesis is introduced.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS.FullNetworkForm

/-- The discount accumulated during one holding time. -/
noncomputable def finiteTraceHoldingDiscount (alpha t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-alpha * t))

/-- The discounted reward earned during one holding interval.  The truncated
subtraction only affects negative times, a null set under an exponential law. -/
noncomputable def finiteTraceHoldingReward (alpha t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / alpha) * (1 - finiteTraceHoldingDiscount alpha t)

theorem measurable_finiteTraceHoldingDiscount (alpha : ℝ) :
    Measurable (finiteTraceHoldingDiscount alpha) := by
  unfold finiteTraceHoldingDiscount
  fun_prop

theorem measurable_finiteTraceHoldingReward (alpha : ℝ) :
    Measurable (finiteTraceHoldingReward alpha) := by
  unfold finiteTraceHoldingReward
  exact measurable_const.mul
    (measurable_const.sub (measurable_finiteTraceHoldingDiscount alpha))

/-- Exact mean discounted reward of one `Exponential(r)` holding time. -/
theorem lintegral_expMeasure_holdingReward {r alpha : ℝ}
    (hr : 0 < r) (halpha : 0 < alpha) :
    (∫⁻ t : ℝ, finiteTraceHoldingReward alpha t ∂expMeasure r) =
      ENNReal.ofReal (1 / (r + alpha)) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  change (∫⁻ t : ℝ, ENNReal.ofReal (1 / alpha) *
    (1 - finiteTraceHoldingDiscount alpha t) ∂expMeasure r) = _
  change (∫⁻ t : ℝ, ENNReal.ofReal (1 / alpha) *
    ((1 : ℝ → ℝ≥0∞) - finiteTraceHoldingDiscount alpha) t ∂expMeasure r) = _
  have hdisc : (∫⁻ t : ℝ, finiteTraceHoldingDiscount alpha t ∂expMeasure r) =
      ENNReal.ofReal (r / (r + alpha)) := by
    simpa [finiteTraceHoldingDiscount] using
      ReflectedGMS.DiscountedTraceStep.lintegral_expMeasure_discount hr halpha.le
  have hdisc_ne :
      (∫⁻ t : ℝ, finiteTraceHoldingDiscount alpha t ∂expMeasure r) ≠ ∞ := by
    rw [hdisc]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.lintegral_const_mul
    (f := (1 : ℝ → ℝ≥0∞) - finiteTraceHoldingDiscount alpha)
    (ENNReal.ofReal (1 / alpha))
    (measurable_const.sub (measurable_finiteTraceHoldingDiscount alpha))]
  change ENNReal.ofReal (1 / alpha) *
    (∫⁻ a : ℝ, 1 - finiteTraceHoldingDiscount alpha a ∂expMeasure r) = _
  rw [MeasureTheory.lintegral_sub (μ := expMeasure r)
    (f := fun _ : ℝ => (1 : ℝ≥0∞))
    (g := finiteTraceHoldingDiscount alpha)
    (measurable_finiteTraceHoldingDiscount alpha) hdisc_ne
    (by
      have ht : ∀ᵐ t ∂expMeasure r, 0 < t := by
        rw [ae_iff]
        have hs : {t : ℝ | ¬ 0 < t} = Set.Iic 0 := by
          ext t
          simp
        rw [hs]
        exact ReflectedWalk.Theorem16.expMeasure_Iic_zero hr
      filter_upwards [ht] with t ht
      exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le) ht.le)))]
  rw [lintegral_const, measure_univ, one_mul,
    hdisc]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub]
  · rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr halpha.le)]
    congr 1
    field_simp [halpha.ne', (add_pos hr halpha).ne']
    ring
  · exact div_nonneg hr.le (add_pos hr halpha).le

open ReflectedWalk

variable {S : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S]

/-- Conditionally on an embedded path, the actual holding kernel gives the
exact one-coordinate discounted reward. -/
theorem lintegral_holdingKernel_holdingReward
    {w : S → ℝ} (hw : ∀ z, 0 < w z) (y : ℕ → S) (n : ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) :
    (∫⁻ t : ℕ → ℝ, finiteTraceHoldingReward alpha (t n) ∂holdingKernel w y) =
      ENNReal.ofReal (1 / (w (y n) + alpha)) := by
  letI (i : ℕ) : IsProbabilityMeasure (expMeasure (w (y i))) :=
    isProbabilityMeasure_expMeasure (hw (y i))
  rw [holdingKernel_apply hw y]
  rw [← lintegral_map (measurable_finiteTraceHoldingReward alpha)
    (measurable_pi_apply n), Measure.infinitePi_map_eval]
  exact lintegral_expMeasure_holdingReward (hw (y n)) halpha

/-- The first actual reward under the existing embedded-chain/holding-time
joint law.  In particular this verifies the inhomogeneous term of the renewal
equation directly from `chainLaw ⊗ₘ holdingKernel`. -/
theorem lintegral_chainLaw_compProd_firstReward
    (κ : Kernel S S) [IsMarkovKernel κ] (w : S → ℝ) (hw : ∀ z, 0 < w z)
    (F : S → ℝ) (x : S) {alpha : ℝ} (halpha : 0 < alpha) :
    (∫⁻ p : (ℕ → S) × (ℕ → ℝ),
      ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0)
        ∂(MarkovChain.chainLaw κ x ⊗ₘ holdingKernel w)) =
      ENNReal.ofReal (F x) * ENNReal.ofReal (1 / (w x + alpha)) := by
  have hy0 : Measurable (fun y : ℕ → S => y 0) := measurable_pi_apply 0
  have ht0 : Measurable (fun t : ℕ → ℝ => t 0) := measurable_pi_apply 0
  have hFm : Measurable (fun y : ℕ → S => ENNReal.ofReal (F (y 0))) :=
    ((measurable_of_countable F).comp hy0).ennreal_ofReal
  have hRm : Measurable (fun t : ℕ → ℝ => finiteTraceHoldingReward alpha (t 0)) :=
    (measurable_finiteTraceHoldingReward alpha).comp ht0
  have hmeas : Measurable (fun p : (ℕ → S) × (ℕ → ℝ) =>
      ENNReal.ofReal (F (p.1 0)) * finiteTraceHoldingReward alpha (p.2 0)) := by
    exact (hFm.comp measurable_fst).mul (hRm.comp measurable_snd)
  rw [Measure.lintegral_compProd hmeas]
  apply Eq.trans (lintegral_congr fun y => by
    rw [MeasureTheory.lintegral_const_mul
      (f := fun t : ℕ → ℝ => finiteTraceHoldingReward alpha (t 0))
      (ENNReal.ofReal (F (y 0))) hRm,
      lintegral_holdingKernel_holdingReward hw y 0 halpha])
  calc
    (∫⁻ y : ℕ → S, ENNReal.ofReal (F (y 0)) *
        ENNReal.ofReal (1 / (w (y 0) + alpha)) ∂MarkovChain.chainLaw κ x) =
        ∫⁻ _y : ℕ → S, ENNReal.ofReal (F x) *
          ENNReal.ofReal (1 / (w x + alpha)) ∂MarkovChain.chainLaw κ x := by
      refine lintegral_congr_ae ?_
      filter_upwards [MarkovChain.chainLaw_ae_start κ x] with y hy
      rw [hy]
    _ = _ := by simp

end ReflectedGMS.FullNetworkForm
