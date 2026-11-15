import LatticeProb.Prob.RandomFiniteSelectionMeasurable
import Mathlib.Probability.Independence.Basic

/-! # Independent finite selections -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

/-- A finite random selection of bad events satisfies the product union bound
when the selection and the random element are independent. -/
theorem measure_exists_mem_finset_le_of_indepFun
    {Ω β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : Ω → Finset ι} {Y : Ω → β} (hK : Measurable K) (hY : Measurable Y)
    (hKY : IndepFun K Y P) (B : ι → Set β) (hBm : ∀ i, MeasurableSet (B i))
    (p : ℝ≥0∞) (N : ℕ) (hB : ∀ i, P {ω | Y ω ∈ B i} ≤ p) :
    P {ω | ∃ i ∈ K ω, Y ω ∈ B i} ≤
      P {ω | N < (K ω).card} + (N : ℝ≥0∞) * p := by
  have hEm : MeasurableSet {z : Finset ι × β | ∃ i ∈ id z.1, z.2 ∈ B i} :=
    measurableSet_exists_mem_finset id B
      (fun i => measurableSet_setOfPred.mpr (measurable_finset_mem i)) hBm
  have hbad : ∀ i, (P.map Y) (B i) ≤ p := by
    intro i
    rw [Measure.map_apply hY (hBm i)]
    exact hB i
  have hbound := prod_measure_exists_mem_finset_le_of_measurable
    (P.map K) (P.map Y) id B p N measurable_id hBm hbad
  have hjoint := hKY.map_prod_eq_prod_map_map hK.aemeasurable hY.aemeasurable
  have htail : MeasurableSet {s : Finset ι | N < (id s).card} :=
    measurableSet_lt measurable_const (measurable_of_countable Finset.card)
  rw [← hjoint, Measure.map_apply (hK.prodMk hY) hEm,
    Measure.map_apply hK htail] at hbound
  exact hbound

end LatticeProb
