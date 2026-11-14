import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.MetricSpace.Bounded

/-! # Continuous maps with unbounded range -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

variable {T X : Type*} [TopologicalSpace T] [PseudoMetricSpace X]

/-- Continuous maps whose ranges are unbounded form a Borel subset of the
compact-open function space. -/
theorem measurableSet_continuousMap_unbounded_range
    [MeasurableSpace C(T, X)] [BorelSpace C(T, X)] (x : X) :
    MeasurableSet {f : C(T, X) | ¬ Bornology.IsBounded (Set.range f)} := by
  have hclosed (n : ℕ) : IsClosed {f : C(T, X) | ∀ t, dist (f t) x ≤ (n : ℝ)} := by
    simpa only [ofPred_forall] using
      (isClosed_iInter fun t : T =>
        isClosed_le ((continuous_eval_const t).dist continuous_const) continuous_const)
  have heq : {f : C(T, X) | Bornology.IsBounded (Set.range f)} =
      ⋃ n : ℕ, {f : C(T, X) | ∀ t, dist (f t) x ≤ (n : ℝ)} := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hf
      obtain ⟨r, hr⟩ := hf.subset_ball x
      obtain ⟨n, hn⟩ := exists_nat_gt r
      refine ⟨n, fun t => ?_⟩
      exact le_of_lt ((hr ⟨t, rfl⟩).trans hn)
    · rintro ⟨n, hn⟩
      apply (isBounded_closedBall : Bornology.IsBounded (closedBall x (n : ℝ))).subset
      rintro _ ⟨t, rfl⟩
      exact hn t
  have hm : MeasurableSet {f : C(T, X) | Bornology.IsBounded (Set.range f)} := by
    rw [heq]
    exact MeasurableSet.iUnion fun n => (hclosed n).measurableSet
  exact hm.compl

end LatticeProb
