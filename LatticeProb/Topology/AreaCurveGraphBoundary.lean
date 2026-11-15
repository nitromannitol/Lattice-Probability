import LatticeProb.Topology.AreaCurveOpenCoverage
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Inner graph boundaries of area-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- An inside point and an outside point determine a frontier point no farther
from the inside point than the outside point is. -/
theorem exists_frontier_dist_le_of_mem_closure_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {x y : E} (hx : x ∈ closure U) (hy : y ∉ U) :
    ∃ z ∈ frontier U, dist x z ≤ dist x y := by
  by_cases hxU : x ∈ U
  · have hne : U ≠ univ := by
      intro h
      exact hy (h ▸ mem_univ y)
    obtain ⟨z, hz, heq⟩ := exists_mem_frontier_infDist_compl_eq_dist hxU hne
    exact ⟨z, hz, heq ▸ Metric.infDist_le_dist_of_mem hy⟩
  · exact ⟨x, ⟨hx, by simpa only [hU.interior_eq] using hxU⟩, by simp⟩

/-- An inner boundary vertex for a curve-segment interval lies within the
length of a crossing edge of the frontier of the open segment domain. -/
theorem area_curve_innerBoundary_near_frontier
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (G : SimpleGraph V) (r : V → ℝ) {U : Set E} (hU : IsOpen U)
    {a b : ℝ} (hab : a < b) (himage : η '' Icc a b = closure U)
    {v w : V} (hv : r v ∈ Icc a b) (hvw : G.Adj v w)
    (hw : r w ∉ Icc a b) {δ : ℝ}
    (hbound : ∀ x y, G.Adj x y → r x ∈ Icc a b → r y ∉ Icc a b →
      dist (η (r x)) (η (r y)) ≤ δ) :
    ∃ z ∈ frontier U, dist (η (r v)) z ≤ δ := by
  have hin : η (r v) ∈ closure U := himage ▸ ⟨r v, hv, rfl⟩
  have hout : η (r w) ∉ U := by
    intro h
    have := preimage_open_subset_Ioo_of_area_curve_coverage η μ hη hμ hU hab
      (by rw [himage]; exact subset_closure) h
    exact hw ⟨this.1.le, this.2.le⟩
  obtain ⟨z, hz, hdist⟩ := exists_frontier_dist_le_of_mem_closure_of_not_mem hU hin hout
  exact ⟨z, hz, hdist.trans (hbound v w hvw hv hw)⟩

end LatticeProb
