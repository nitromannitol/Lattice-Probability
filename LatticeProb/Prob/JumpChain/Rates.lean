import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith

/-!
# Uniformization of bounded jump rates

A nonnegative rate matrix with uniformly bounded row sums defines a discrete Markov
kernel by adding holding probability on the diagonal. The state space is countable
with measurable singletons; no finite support condition is imposed on its rows.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Jump rates with a uniform bound `R` on the total rate. -/
structure BoundedRates (S : Type*) where
  q : S → S → ℝ
  q_nonneg : ∀ i j, 0 ≤ q i j
  q_self : ∀ i, q i i = 0
  summable : ∀ i, Summable (q i)
  R : ℝ
  R_pos : 0 < R
  total_le : ∀ i, ∑' j, q i j ≤ R

variable {S : Type*}

namespace BoundedRates

/-- The transition probability of the chain sampled at clock rings of rate `R`. -/
def p (rates : BoundedRates S) (i j : S) : ℝ := by
  classical
  exact if j = i then 1 - (∑' k, rates.q i k) / rates.R else rates.q i j / rates.R

/-- Every uniformized transition probability is nonnegative. -/
theorem p_nonneg (rates : BoundedRates S) (i j : S) : 0 ≤ rates.p i j := by
  classical
  unfold p
  split_ifs
  · exact sub_nonneg.mpr ((div_le_one rates.R_pos).mpr (rates.total_le i))
  · exact div_nonneg (rates.q_nonneg i j) rates.R_pos.le

/-- Separate the diagonal correction from the scaled rate matrix. -/
theorem p_eq_add (rates : BoundedRates S) (i j : S) :
    rates.p i j =
      (if j = i then 1 - (∑' k, rates.q i k) / rates.R else 0) +
        rates.q i j / rates.R := by
  classical
  by_cases h : j = i
  · subst j
    simp only [p, ite_true, rates.q_self, zero_div, add_zero]
  · simp only [p, if_neg h, zero_add]

/-- A row of the uniformized transition matrix sums to one. -/
theorem hasSum_p (rates : BoundedRates S) (i : S) : HasSum (rates.p i) 1 := by
  classical
  have h := (hasSum_ite_eq i (1 - (∑' k, rates.q i k) / rates.R)).add
    ((rates.summable i).hasSum.div_const rates.R)
  have hsum : 1 - (∑' k, rates.q i k) / rates.R +
      (∑' k, rates.q i k) / rates.R = 1 := sub_add_cancel _ _
  rw [hsum] at h
  exact h.congr_fun (fun j ↦ rates.p_eq_add i j)

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The probability kernel obtained by uniformizing the rate matrix. -/
def kernel (rates : BoundedRates S) : Kernel S S :=
  Kernel.ofFunOfCountable fun i ↦
    Measure.sum fun j ↦ ENNReal.ofReal (rates.p i j) • Measure.dirac j

/-- Uniformization gives a Markov kernel, including rows with infinitely many targets. -/
instance isMarkovKernel_kernel (rates : BoundedRates S) : IsMarkovKernel rates.kernel where
  isProbabilityMeasure i :=
    HasSum.isProbabilityMeasure_sum_dirac (rates.p_nonneg i) (rates.hasSum_p i)

/-- The mass at a singleton is the specified transition probability. -/
theorem kernel_singleton (rates : BoundedRates S) (i j : S) :
    rates.kernel i {j} = ENNReal.ofReal (rates.p i j) := by
  exact Measure.sum_smul_dirac_singleton

end BoundedRates

end

end LatticeProb.JumpChain
