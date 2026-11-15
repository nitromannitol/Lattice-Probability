import LatticeProb.Topology.AreaCurveRegularClosed
import LatticeProb.Analysis.AreaParametrizedCurveCells

/-! # Shared frontiers of area curve segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Regular closed sets with disjoint interiors meet precisely on their shared frontier. -/
theorem inter_eq_frontier_inter_frontier_of_regularClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B)
    (hdis : Disjoint (interior A) (interior B)) :
    A ∩ B = frontier A ∩ frontier B := by
  have hAc : IsClosed A := hA ▸ isClosed_closure
  have hBc : IsClosed B := hB ▸ isClosed_closure
  have hAB : Disjoint A (interior B) := by
    rw [← hA]
    exact hdis.closure_left isOpen_interior
  have hBA : Disjoint (interior A) B := by
    rw [← hB]
    exact hdis.closure_right isOpen_interior
  apply Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    exact ⟨⟨hAc.closure_eq.symm ▸ hxA, fun hx => (disjoint_left.mp hBA) hx hxB⟩,
      ⟨hBc.closure_eq.symm ▸ hxB, fun hx => (disjoint_left.mp hAB) hxA hx⟩⟩
  · rintro x ⟨hxA, hxB⟩
    exact ⟨hAc.closure_eq ▸ frontier_subset_closure hxA,
      hBc.closure_eq ▸ frontier_subset_closure hxB⟩

/-- Ordered nondegenerate segments of an area curve meet precisely on their shared frontier,
provided both segment images are regular closed. -/
theorem area_curve_inter_eq_shared_frontier
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : ℝ → X) (μ : Measure X)
    (hc : Continuous η) (hs : Surjective η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (hA : closure (interior (η '' Icc a b)) = η '' Icc a b)
    (hB : closure (interior (η '' Icc c d)) = η '' Icc c d) :
    η '' Icc a b ∩ η '' Icc c d =
      frontier (η '' Icc a b) ∩ frontier (η '' Icc c d) := by
  apply inter_eq_frontier_inter_frontier_of_regularClosed hA hB
  rw [disjoint_iff_inter_eq_empty]
  exact eq_empty_of_isOpen_subset_image_Icc_inter hc hs hμ hab hbc hcd
    (isOpen_interior.inter isOpen_interior) (inter_subset_inter interior_subset interior_subset)

/-- For a proper surjective area curve the shared-frontier identity holds for every pair of
ordered nondegenerate segments. -/
theorem proper_area_curve_inter_eq_shared_frontier
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (η : ℝ → X) (μ : Measure X)
    (hc : Continuous η) (hp : IsProperMap η) (hs : Surjective η)
    (hmap : Measure.map η volume = μ)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    η '' Icc a b ∩ η '' Icc c d =
      frontier (η '' Icc a b) ∩ frontier (η '' Icc c d) :=
  area_curve_inter_eq_shared_frontier η μ hc hs hμ hab hbc hcd
    (closure_interior_image_Icc_of_proper_area_curve η μ hc hp hs hmap hμ hab)
    (closure_interior_image_Icc_of_proper_area_curve η μ hc hp hs hmap hμ hcd)

end LatticeProb
