/- Measurability of strict positivity throughout a compact set.

Moved from Parking-Sharpness.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Bases
import Mathlib.Data.Rat.Encodable

open MeasureTheory Set TopologicalSpace
namespace LatticeProb.Scaling.CompactPositivity

/-- The event that a continuous field is everywhere strictly positive on a compact separable
space is measurable, tested on a countable dense subset. -/
theorem measurableSet_forall_pos
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [CompactSpace X] [SeparableSpace X]
    {u : Ω → X → ℝ} (hu : ∀ ω, Continuous (u ω))
    (hum : ∀ x, Measurable fun ω => u ω x) :
    MeasurableSet {ω | ∀ x, 0 < u ω x} := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  have heq : {ω | ∀ x, 0 < u ω x} =
      ⋃ q : ℚ, {ω | (0 : ℝ) < q} ∩ ⋂ x ∈ D, {ω | (q : ℝ) ≤ u ω x} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      by_cases hX : Nonempty X
      · obtain ⟨x, _, hmin⟩ := isCompact_univ.exists_isMinOn (Set.nonempty_iff_univ_nonempty.mp hX)
          (hu ω).continuousOn
        obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn (h x)
        exact ⟨q, hq0, fun y _ => hqx.le.trans (hmin (mem_univ y))⟩
      · exact ⟨1, by norm_num, fun x _ => (hX ⟨x⟩).elim⟩
    · rintro ⟨q, hq, hD⟩ x
      have hl : (q : ℝ) ≤ u ω x :=
        closure_minimal hD (isClosed_le continuous_const (hu ω)) (hDd x)
      exact hq.trans_le hl
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  exact (MeasurableSet.const _).inter
    (MeasurableSet.biInter hDc fun x _ => measurableSet_le measurable_const (hum x))

end LatticeProb.Scaling.CompactPositivity
