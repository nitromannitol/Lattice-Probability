import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Almost sure positivity of a conditional probability

Let `m ≤ m0` be a sub-sigma-algebra and `A` an event. The conditional probability `P[1_A | m]` is almost surely
positive as soon as `A` meets every event of `m` of positive probability in a set of positive probability:

* `LatticeProb.ae_condExp_indicator_pos_of_forall_measure_inter_eq_zero`: if `P (A ∩ B) = 0` implies `P B = 0`
  for every `B` measurable for `m`, then `0 < P[1_A | m]` almost surely.

This reduces conditional positivity statements (for instance for Gaussian fields with the domain Markov property)
to a statement about null sets of rectangles `A ∩ B`.
-/

open MeasureTheory

namespace LatticeProb

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- If an event `A` meets every event `B` of the sub-sigma-algebra `m` with `P B > 0` in a set of positive
probability, then the conditional probability of `A` given `m` is almost surely positive. -/
theorem ae_condExp_indicator_pos_of_forall_measure_inter_eq_zero [IsFiniteMeasure P] (hm : m ≤ m0) {A : Set Ω}
    (hA : MeasurableSet A) (h : ∀ B : Set Ω, MeasurableSet[m] B → P (A ∩ B) = 0 → P B = 0) :
    ∀ᵐ ω ∂P, 0 < (P[A.indicator (1 : Ω → ℝ) | m]) ω := by
  set g : Ω → ℝ := P[A.indicator (1 : Ω → ℝ) | m] with hg
  have hgm : StronglyMeasurable[m] g := stronglyMeasurable_condExp
  have hB : MeasurableSet[m] {ω | g ω ≤ 0} := hgm.measurable measurableSet_Iic
  have hint : Integrable (A.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have h1 : ∫ ω in {ω | g ω ≤ 0}, g ω ∂P = ∫ ω in {ω | g ω ≤ 0}, A.indicator (1 : Ω → ℝ) ω ∂P :=
    setIntegral_condExp hm hint hB
  have h2 : ∫ ω in {ω | g ω ≤ 0}, g ω ∂P ≤ 0 := setIntegral_nonpos (hm _ hB) fun ω hω => hω
  have h3 : ∫ ω in {ω | g ω ≤ 0}, A.indicator (1 : Ω → ℝ) ω ∂P = (P (A ∩ {ω | g ω ≤ 0})).toReal := by
    rw [integral_indicator_one hA, Measure.real, Measure.restrict_apply hA]
  have h4 : (P (A ∩ {ω | g ω ≤ 0})).toReal = 0 :=
    le_antisymm (by rw [← h3, ← h1]; exact h2) ENNReal.toReal_nonneg
  have h5 : P (A ∩ {ω | g ω ≤ 0}) = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp h4 |>.resolve_right (measure_ne_top P _)
  have h6 : P {ω | g ω ≤ 0} = 0 := h _ hB h5
  exact (measure_eq_zero_iff_ae_notMem.mp h6).mono fun ω hω => not_le.mp hω

end LatticeProb
