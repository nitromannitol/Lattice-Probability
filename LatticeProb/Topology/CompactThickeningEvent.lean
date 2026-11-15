import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # Compact sets contained in thickenings -/

open Set Metric TopologicalSpace MeasureTheory

namespace LatticeProb

/-- For a compact set, containment in a thickening is open in the Hausdorff metric. -/
theorem isOpen_compact_subset_thickening {X : Type*} [MetricSpace X]
    {S : Set X} (hS : IsCompact S) (r : ℝ) :
    IsOpen {K : NonemptyCompacts X | S ⊆ thickening r (K : Set X)} := by
  by_cases hne : S.Nonempty
  · apply Metric.isOpen_iff.mpr
    intro K hK
    obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne (continuous_infDist_pt (K : Set X)).continuousOn
    have hlt : infDist x (K : Set X) < r :=
      (mem_thickening_iff_infDist_lt K.nonempty).mp (hK hx)
    refine ⟨r - infDist x (K : Set X), sub_pos.mpr hlt, ?_⟩
    intro L hL y hy
    apply (mem_thickening_iff_infDist_lt L.nonempty).mpr
    have hdist : infDist y (L : Set X) ≤ infDist y (K : Set X) + dist K L := by
      exact infDist_le_infDist_add_hausdorffDist (edist_ne_top K L)
    have hxy : infDist y (K : Set X) ≤ infDist x (K : Set X) := hmax hy
    have hball : dist K L < r - infDist x (K : Set X) := by
      simpa only [Metric.mem_ball, dist_comm] using hL
    linarith
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hSempty, empty_subset, ofPred_true, isOpen_univ]

/-- A measurable nonempty compact random set admits measurable compact containment tests. -/
theorem measurableSet_compact_subset_thickening {X Ω : Type*} [MetricSpace X]
    [MeasurableSpace Ω] [MeasurableSpace (NonemptyCompacts X)]
    [BorelSpace (NonemptyCompacts X)] {K : Ω → NonemptyCompacts X} (hK : Measurable K)
    {S : Set X} (hS : IsCompact S) (r : ℝ) :
    MeasurableSet {ω | S ⊆ thickening r (K ω : Set X)} :=
  hK (isOpen_compact_subset_thickening hS r).measurableSet

end LatticeProb
