import LatticeProb.Prob.JumpChain.Semigroup
import LatticeProb.Prob.JumpChain.OperatorExponential
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Uniformization as an operator exponential

Markov kernels act by contraction on bounded functions, realized here as `lp` at infinity.
The Poisson mixture is the exponential of its bounded jump generator. Consequently,
changing the dominating clock rate leaves every transition measure unchanged.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {S : Type*}

/-- Bounded real observables with the supremum norm. -/
abbrev BoundedObservable (S : Type*) := lp (fun _ : S ↦ ℝ) ∞

/-- Each coordinate of a bounded observable is bounded by its norm. -/
theorem abs_observable_le_norm (f : BoundedObservable S) (i : S) : |f i| ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f i

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Integrating a bounded observable against the rows of a Markov kernel is a contraction. -/
def markovOperator (κ : Kernel S S) [IsMarkovKernel κ] :
    BoundedObservable S →L[ℝ] BoundedObservable S :=
  LinearMap.mkContinuous
    { toFun f := ⟨fun i ↦ ∫ j, f j ∂κ i, memℓp_infty ⟨‖f‖, by
        rintro _ ⟨i, rfl⟩
        exact abs_integral_le (κ i) f (abs_observable_le_norm f)⟩⟩
      map_add' f g := by
        apply lp.ext
        funext i
        exact integral_add (integrable_of_abs_le (κ i) f (abs_observable_le_norm f))
          (integrable_of_abs_le (κ i) g (abs_observable_le_norm g))
      map_smul' c f := by
        apply lp.ext
        funext i
        exact integral_const_mul c (fun j ↦ f j) }
    1 (fun f ↦ by
      rw [one_mul]
      apply lp.norm_le_of_forall_le (norm_nonneg f)
      intro i
      exact abs_integral_le (κ i) f (abs_observable_le_norm f))

/-- Evaluation of the Markov operator is row integration. -/
theorem markovOperator_apply (κ : Kernel S S) [IsMarkovKernel κ]
    (f : BoundedObservable S) (i : S) :
    markovOperator κ f i = ∫ j, f j ∂κ i := rfl

/-- Operator powers integrate against the corresponding discrete kernel powers. -/
theorem markovOperator_pow_apply (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ)
    (f : BoundedObservable S) (i : S) :
    (markovOperator κ ^ n) f i = ∫ j, f j ∂(κ ^ n) i := by
  induction n generalizing f with
  | zero =>
    change f i = ∫ j, f j ∂Measure.dirac i
    exact (integral_dirac f i).symm
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, pow_succ']
    exact (Kernel.integral_comp
      (integrable_of_abs_le _ f (abs_observable_le_norm f))).symm

/-- The operator exponential evaluates as the exponential generating series of discrete powers. -/
theorem exp_markovOperator_apply (κ : Kernel S S) [IsMarkovKernel κ]
    (x : ℝ) (f : BoundedObservable S) (i : S) :
    NormedSpace.exp (x • markovOperator κ) f i =
      ∑' n : ℕ, (∫ j, f j ∂(κ ^ n) i) / n.factorial * x ^ n := by
  let L := (lp.evalCLM ℝ (fun _ : S ↦ ℝ) ∞ i).comp
    (ContinuousLinearMap.apply ℝ (BoundedObservable S) f)
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (x • markovOperator κ)).map L.toAddMonoidHom L.continuous
  apply h.tsum_eq.symm.trans
  apply tsum_congr
  intro n
  change ((n.factorial : ℝ)⁻¹ • (x • markovOperator κ) ^ n) f i = _
  change (((n.factorial : ℝ)⁻¹) • (((x • markovOperator κ) ^ n) f)) i = _
  rw [operator_smul_pow_apply]
  change (n.factorial : ℝ)⁻¹ * (x ^ n * ((markovOperator κ ^ n) f i)) = _
  rw [markovOperator_pow_apply]
  ring

namespace BoundedRates

/-- The bounded generator acting on bounded real observables. -/
def generatorOperator (rates : BoundedRates S) :
    BoundedObservable S →L[ℝ] BoundedObservable S :=
  rates.R • (markovOperator rates.kernel - 1)

/-- The bounded generator has the exact rate-weighted increment formula. -/
theorem generatorOperator_apply (rates : BoundedRates S) (f : BoundedObservable S) (i : S) :
    rates.generatorOperator f i = ∑' j, rates.q i j * (f j - f i) := by
  change rates.R * ((∫ j, f j ∂rates.kernel i) - f i) = _
  rw [rates.integral_kernel i f (abs_observable_le_norm f)]
  exact rates.uniformized_generator i f (abs_observable_le_norm f)

/-- The bounded generator depends only on the rates, not on the chosen domination constant. -/
theorem generatorOperator_eq (rates other : BoundedRates S) (hq : rates.q = other.q) :
    rates.generatorOperator = other.generatorOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  rw [rates.generatorOperator_apply, other.generatorOperator_apply, hq]

/-- The Poisson transition operator is exactly the exponential of the bounded generator. -/
theorem exp_generatorOperator_apply (rates : BoundedRates S) (t : ℝ≥0)
    (f : BoundedObservable S) (i : S) :
    NormedSpace.exp ((t : ℝ) • rates.generatorOperator) f i =
      ∫ j, f j ∂rates.transitionKernel t i := by
  have hscale : (t : ℝ) • rates.generatorOperator =
      (rates.R * t) • (markovOperator rates.kernel - 1) := by
    simp only [generatorOperator, smul_smul, mul_comm]
  rw [hscale, exp_smul_sub_one]
  change Real.exp (-(rates.R * t)) *
    (NormedSpace.exp ((rates.R * t) • markovOperator rates.kernel) f i) = _
  rw [exp_markovOperator_apply, rates.integral_transitionKernel t i f
    (abs_observable_le_norm f)]

/-- The transition kernel is independent of the positive dominating rate. -/
theorem transitionKernel_eq (rates other : BoundedRates S) (hq : rates.q = other.q)
    (t : ℝ≥0) : rates.transitionKernel t = other.transitionKernel t := by
  classical
  ext i : 1
  apply Measure.ext_of_singleton
  intro j
  let f : BoundedObservable S := ⟨fun k ↦ if k = j then 1 else 0,
    memℓp_infty ⟨1, by
      rintro _ ⟨k, rfl⟩
      change ‖if k = j then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num⟩⟩
  have heq := congrArg (fun A : BoundedObservable S →L[ℝ] BoundedObservable S ↦
    NormedSpace.exp ((t : ℝ) • A) f i) (rates.generatorOperator_eq other hq)
  rw [rates.exp_generatorOperator_apply, other.exp_generatorOperator_apply] at heq
  change (∫ k, ({j} : Set S).indicator 1 k ∂rates.transitionKernel t i) =
    (∫ k, ({j} : Set S).indicator 1 k ∂other.transitionKernel t i) at heq
  rw [integral_indicator_one (measurableSet_singleton j),
    integral_indicator_one (measurableSet_singleton j)] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq

end BoundedRates

end

end LatticeProb.JumpChain
