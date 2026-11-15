import LatticeProb.Prob.RandomScaleProductUnion

/-! # Measurability of finite random selections -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A countable union of measurable events selected by a measurable finite set
is measurable on the product space. -/
theorem measurableSet_exists_mem_finset {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    (K : α → Finset ι) (B : ι → Set β)
    (hK : ∀ i, MeasurableSet {x | i ∈ K x})
    (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet {z : α × β | ∃ i ∈ K z.1, z.2 ∈ B i} := by
  have heq : {z : α × β | ∃ i ∈ K z.1, z.2 ∈ B i} =
      ⋃ i, ({x | i ∈ K x} ×ˢ B i) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hK i).prod (hB i)

/-- The cardinality of a finite selection is measurable when its membership
indicators are measurable and its index set is countable. -/
theorem measurable_finset_card_of_membership {α ι : Type*}
    [MeasurableSpace α] [Countable ι] (K : α → Finset ι)
    (hK : ∀ i, MeasurableSet {x | i ∈ K x}) :
    Measurable fun x => (K x).card := by
  have hKm : Measurable K := measurable_finset_iff.mpr fun i =>
    measurableSet_setOfPred.mp (hK i)
  exact (measurable_of_countable (Finset.card : Finset ι → ℕ)).comp hKm

/-- Finite integer intervals with measurable endpoints form a measurable
finite-set-valued map, including when the endpoints are reversed. -/
theorem measurable_finset_Icc_int {α : Type*} [MeasurableSpace α]
    {a b : α → ℤ} (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => Finset.Icc (a x) (b x) := by
  exact (measurable_of_countable (fun p : ℤ × ℤ => Finset.Icc p.1 p.2)).comp
    (ha.prodMk hb)

/-- A product-law bound with measurable random indices and measurable bad events. -/
theorem prod_measure_exists_mem_finset_le_of_measurable {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable ι]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Finset ι) (B : ι → Set β) (p : ℝ≥0∞) (N : ℕ)
    (hK : Measurable K) (hBm : ∀ i, MeasurableSet (B i))
    (hB : ∀ i, ν (B i) ≤ p) :
    (μ.prod ν) {z : α × β | ∃ i ∈ K z.1, z.2 ∈ B i} ≤
      μ {x | N < (K x).card} + (N : ℝ≥0∞) * p := by
  have hmem : ∀ i, MeasurableSet {x | i ∈ K x} := fun i =>
    measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp hK)
  have hcard := measurable_finset_card_of_membership K hmem
  exact prod_measure_exists_mem_finset_le μ ν K B p N hB
    (measurableSet_exists_mem_finset K B hmem hBm)
    (measurableSet_le hcard measurable_const)

end LatticeProb
