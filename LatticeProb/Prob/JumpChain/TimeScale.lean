import LatticeProb.Prob.JumpChain.Operator
import LatticeProb.Prob.JumpChain.Semigroup

/-!
# Time changes from scaling jump rates

Multiplying all jump rates by a positive constant multiplies the bounded generator
by that constant. The operator exponential then identifies the transition kernel
with the original kernel evaluated at the correspondingly scaled time.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Scaling every jump rate scales the bounded generator by the same constant. -/
theorem generatorOperator_eq_smul (rates rates' : BoundedRates S) (c : ℝ)
    (hq : ∀ i j, rates'.q i j = c * rates.q i j) :
    rates'.generatorOperator = c • rates.generatorOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  change rates'.generatorOperator f i = c * rates.generatorOperator f i
  rw [rates'.generatorOperator_apply, rates.generatorOperator_apply, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [hq]
  exact mul_assoc _ _ _

/-- Multiplying all jump rates by a positive constant is a deterministic time change. -/
theorem transitionKernel_eq_timeScale (rates rates' : BoundedRates S) (c : ℝ)
    (hc : 0 < c) (hq : ∀ i j, rates'.q i j = c * rates.q i j) (t : ℝ≥0) :
    rates'.transitionKernel t = rates.transitionKernel (⟨c, hc.le⟩ * t) := by
  classical
  have hgen : (t : ℝ) • rates'.generatorOperator =
      ((⟨c, hc.le⟩ * t : ℝ≥0) : ℝ) • rates.generatorOperator := by
    change (t : ℝ) • rates'.generatorOperator =
      (c * (t : ℝ)) • rates.generatorOperator
    rw [generatorOperator_eq_smul rates rates' c hq, smul_smul, mul_comm]
  ext i : 1
  apply Measure.ext_of_singleton
  intro j
  let f : BoundedObservable S := ⟨fun k ↦ if k = j then 1 else 0,
    memℓp_infty ⟨1, by
      rintro _ ⟨k, rfl⟩
      change ‖if k = j then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num⟩⟩
  have heq := congrArg (fun A : BoundedObservable S →L[ℝ] BoundedObservable S ↦
    NormedSpace.exp A f i) hgen
  rw [rates'.exp_generatorOperator_apply, rates.exp_generatorOperator_apply] at heq
  change (∫ k, ({j} : Set S).indicator 1 k ∂rates'.transitionKernel t i) =
    (∫ k, ({j} : Set S).indicator 1 k
      ∂rates.transitionKernel (⟨c, hc.le⟩ * t) i) at heq
  rw [integral_indicator_one (measurableSet_singleton j),
    integral_indicator_one (measurableSet_singleton j)] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp heq

end

end LatticeProb.JumpChain.BoundedRates
