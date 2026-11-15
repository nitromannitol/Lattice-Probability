import LatticeProb.Prob.CellConfigLabelTransition
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Defs

/-! # Probability kernel for labelled cell configurations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- Every row of the labelled transition matrix has finite support. -/
theorem finiteSupport_step (H : GMSSpace) (n : ℕ) :
    (Function.support (step H n)).Finite := by
  by_cases h : rowTotal H n = 0
  · apply (Set.finite_singleton n).subset
    intro m hm
    simp only [Function.mem_support, step, h, ↓reduceIte] at hm
    simpa using hm
  · apply (CellConfig.finiteRows_code H.2 n).subset
    intro m hm
    change H.1.codeCond n m ≠ 0
    simp only [Function.mem_support, step, h, ↓reduceIte] at hm
    exact fun hz => hm (by rw [hz, zero_div])

theorem summable_step (H : GMSSpace) (n : ℕ) : Summable (step H n) :=
  summable_of_hasFiniteSupport (finiteSupport_step H n)

/-- The distribution of the next label, jointly measurable in configuration and label. -/
def kernel : Kernel (GMSSpace × ℕ) ℕ where
  toFun p := Measure.sum fun m => ENNReal.ofReal (step p.1 p.2 m) • Measure.dirac m
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    apply Measurable.tsum
    intro m
    have hm : Measurable (fun p : GMSSpace × ℕ => step p.1 p.2 m) := by
      apply measurable_from_prod_countable_left
      intro n
      exact measurable_step n m
    exact hm.ennreal_ofReal.mul measurable_const

theorem kernel_singleton (H : GMSSpace) (n m : ℕ) :
    kernel (H, n) {m} = ENNReal.ofReal (step H n m) := by
  change (Measure.sum fun j => ENNReal.ofReal (step H n j) • Measure.dirac j) {m} = _
  rw [Measure.sum_apply _ (measurableSet_singleton m)]
  rw [tsum_eq_single m]
  · simp
  · intro j hj
    simp [Measure.dirac_apply' _ (measurableSet_singleton m), hj]

instance isMarkovKernel_kernel : IsMarkovKernel kernel := by
  refine ⟨fun p => ⟨?_⟩⟩
  change (Measure.sum fun m => ENNReal.ofReal (step p.1 p.2 m) • Measure.dirac m) univ = 1
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (step_nonneg p.1 p.2) (summable_step p.1 p.2),
    tsum_step, ENNReal.ofReal_one]

end LatticeProb.CellConfigLabelTransition
