import LatticeProb.Topology.CompactCellRadialGap
import LatticeProb.Topology.FiniteCellRadialGap
import LatticeProb.Topology.RadialRestrictionGap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Positive-probability radial gaps -/

set_option autoImplicit false

namespace LatticeProb

open MeasureTheory Set Filter

/-- A locally finite measurable family has, with positive probability, a common
rational interval on which the labels meeting concentric balls do not change. -/
theorem exists_positive_measure_compactCell_radial_gap
    {Ω ι E : Type*} [MeasurableSpace Ω] [Countable ι] [MetricSpace E]
    [MeasurableSpace (TopologicalSpace.NonemptyCompacts E)]
    [BorelSpace (TopologicalSpace.NonemptyCompacts E)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : ι → Ω → TopologicalSpace.NonemptyCompacts E)
    (hC : ∀ i, Measurable (C i)) (z : E) {a b : ℝ} (hab : a < b)
    (hfin : ∀ᵐ ω ∂μ, {i | ((C i ω : Set E) ∩ Metric.ball z b).Nonempty}.Finite) :
    ∃ p q : ℚ, a < (p : ℝ) ∧ (p : ℝ) < q ∧ (q : ℝ) < b ∧
      MeasurableSet {ω | ∀ i, Metric.infDist z (C i ω : Set E) ≤ p ∨
        (q : ℝ) ≤ Metric.infDist z (C i ω : Set E)} ∧
      0 < μ {ω | ∀ i, Metric.infDist z (C i ω : Set E) ≤ p ∨
        (q : ℝ) ≤ Metric.infDist z (C i ω : Set E)} := by
  let I := {pq : ℚ × ℚ | a < (pq.1 : ℝ) ∧ (pq.1 : ℝ) < pq.2 ∧ (pq.2 : ℝ) < b}
  let S : I → Set Ω := fun pq => {ω | ∀ i, Metric.infDist z (C i ω : Set E) ≤ pq.1.1 ∨
    (pq.1.2 : ℝ) ≤ Metric.infDist z (C i ω : Set E)}
  have hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ pq : I, S pq := by
    filter_upwards [hfin] with ω hω
    obtain ⟨p, q, hp, hpq, hq, hgap⟩ :=
      exists_rational_radial_gap_of_finite_inter_ball (fun i => (C i ω : Set E))
        (fun i => (C i ω).nonempty) z hab hω
    exact mem_iUnion.mpr ⟨⟨(p, q), hp, hpq, hq⟩, hgap⟩
  have hunion : μ (⋃ pq : I, S pq) ≠ 0 := by
    intro hzero
    have hnot : ∀ᵐ ω ∂μ, ω ∉ ⋃ pq : I, S pq := (ae_iff).2 (by simpa only [not_not, ofPred_mem_eq] using hzero)
    have hfalse : ∀ᵐ _ω ∂μ, False := by
      filter_upwards [hcover, hnot] with ω hw hn
      exact hn hw
    obtain ⟨_, hf⟩ := hfalse.exists
    exact hf
  obtain ⟨pq, hpq⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  exact ⟨pq.1.1, pq.1.2, pq.2.1, pq.2.2.1, pq.2.2.2,
    measurableSet_compactCell_radial_gap C hC z _ _, hpq⟩

/-- A radial gap also keeps the sets themselves in the same restriction,
including when the enumeration contains repetitions. -/
theorem radial_gap_image_restrictions_constant
    {ι E : Type*} [MetricSpace E] (C : ι → Set E) (hC : ∀ i, (C i).Nonempty)
    (z : E) {a b : ℝ}
    (hgap : ∀ i, Metric.infDist z (C i) ≤ a ∨ b ≤ Metric.infDist z (C i)) :
    ∀ r ∈ Ioo a b, ∀ s ∈ Ioo a b,
      C '' {i | (C i ∩ Metric.ball z r).Nonempty} =
        C '' {i | (C i ∩ Metric.ball z s).Nonempty} := by
  intro r hr s hs
  exact congrArg (Set.image C) ((radial_gap_iff_restrictions_constant C hC z).1 hgap r hr s hs)

end LatticeProb
