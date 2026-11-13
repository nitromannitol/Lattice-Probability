/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupProbabilityKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupKernelComposition
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Probability kernel of the full-form semigroup

For positive summable speed on a countable discrete vertex space, the checked
semigroup coefficients form probability mass functions.  Their associated
measures give a Markov kernel whose singleton masses are exactly those
coefficients.  The analytic Chapman--Kolmogorov identity then becomes ordinary
mathlib kernel composition.

This file constructs only the transition probability kernel determined by the
full-form semigroup.  It does not identify it with a reflected path process or
construct a Hunt realization.
-/

set_option autoImplicit false

open scoped ENNReal NNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The probability mass function given by one row of the full-form semigroup
coefficients. -/
noncomputable def semigroupPMF [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) (x : V) : PMF V :=
  ⟨fun y ↦ ENNReal.ofReal (semigroupKernel G m t x y), by
    apply ENNReal.summable.hasSum_iff.2
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (semigroupKernel_nonneg G m hm t x)
      (summable_semigroupKernel G m hm t x),
      tsum_semigroupKernel_eq_one G m hm hmsum t x]
    simp⟩

@[simp] theorem semigroupPMF_apply [DecidableEq V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) (x y : V) :
    semigroupPMF G m hm hmsum t x y =
      ENNReal.ofReal (semigroupKernel G m t x y) :=
  rfl

/-- The Markov kernel on the countable discrete vertex space obtained from the
full-form semigroup coefficients. -/
noncomputable def semigroupProbabilityKernel [DecidableEq V] [Countable V]
    [MeasurableSpace V] [DiscreteMeasurableSpace V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) : Kernel V V :=
  Kernel.ofFunOfCountable fun x ↦ (semigroupPMF G m hm hmsum t x).toMeasure

instance semigroupProbabilityKernel_isMarkov [DecidableEq V] [Countable V]
    [MeasurableSpace V] [DiscreteMeasurableSpace V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) :
    IsMarkovKernel (semigroupProbabilityKernel G m hm hmsum t) :=
  ⟨fun x ↦ by
    change IsProbabilityMeasure ((semigroupPMF G m hm hmsum t x).toMeasure)
    infer_instance⟩

/-- A singleton has exactly the corresponding semigroup coefficient as its
kernel mass. -/
@[simp] theorem semigroupProbabilityKernel_apply_singleton [DecidableEq V]
    [Countable V] [MeasurableSpace V] [DiscreteMeasurableSpace V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (t : ℝ≥0) (x y : V) :
    semigroupProbabilityKernel G m hm hmsum t x {y} =
      ENNReal.ofReal (semigroupKernel G m t x y) := by
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)

end ReflectedGMS.FullNetworkForm
