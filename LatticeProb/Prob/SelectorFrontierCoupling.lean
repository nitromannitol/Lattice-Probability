import LatticeProb.Prob.SelectorRestrictionCoupling
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening

/-! # Restricting selectors near a frontier -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- Points within `r` of a point outside the `r`-thickened frontier lie on
 the same side of the set. -/
theorem mem_iff_mem_of_not_mem_thickening_frontier
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (outer : Set X) {r : ℝ} {x y : X}
    (hy : y ∉ thickening r (frontier outer)) (hxy : dist x y < r) :
    x ∈ outer ↔ y ∈ outer := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hxy
  have hxball : x ∈ ball y r := hxy
  have hyball : y ∈ ball y r := mem_ball_self hr
  have hcover : ball y r ⊆ interior outer ∪ interior outerᶜ := by
    intro z hz
    have hzfront : z ∉ frontier outer := by
      intro hfront
      apply hy
      exact mem_thickening_iff.mpr ⟨z, hfront, by simpa only [dist_comm] using (show dist z y < r from hz)⟩
    have hzcompl : z ∈ (frontier outer)ᶜ := hzfront
    rw [compl_frontier_eq_union_interior] at hzcompl
    exact hzcompl
  have hdisj : Disjoint (interior outer) (interior outerᶜ) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact (interior_subset hz') (interior_subset hz)
  rcases (convex_ball y r).isPreconnected.subset_or_subset isOpen_interior
      isOpen_interior hdisj hcover with h | h
  · exact iff_of_true (interior_subset (h hxball)) (interior_subset (h hyball))
  · exact iff_of_false (interior_subset (h hxball)) (interior_subset (h hyball))

/-- Restriction adds at most the second marginal's mass in the open
neighborhood of the frontier with radius equal to the coupling tolerance. -/
theorem finitePartitionCoupling_restrictSelector_frontier_error_le
    {X J ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [Fintype ι]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : ι → Set X) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise (fun i j => Disjoint (E i) (E j)))
    (outer : Set X) (f : X → Option J) (r : ℝ) :
    finitePartitionCoupling μ ν E E
      {p | restrictSelector outer f p.1 ≠ restrictSelector outer f p.2 ∨
        r ≤ dist p.1 p.2} ≤
      finitePartitionCoupling μ ν E E
        {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} +
          ν (thickening r (frontier outer)) := by
  apply finitePartitionCoupling_restrictSelector_error_le μ ν E hE hd
    outer (thickening r (frontier outer)) f r
  · intro x y hy hxy
    exact mem_iff_mem_of_not_mem_thickening_frontier outer hy hxy
  · exact isOpen_thickening.measurableSet

end LatticeProb
