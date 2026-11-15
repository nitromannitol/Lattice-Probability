import LatticeProb.Topology.AreaCurveRegularClosed
import LatticeProb.Topology.RationalSegmentConnectedInterior

/-! # Connected interiors of area-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- For a proper surjective area-parametrized curve, connected interiors of all
rational segments imply connected interiors and regular closedness for all
nondegenerate real segments. -/
theorem connected_interior_image_Icc_of_rational_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (hconn : ∀ (p q : ℚ), (p : ℝ) < (q : ℝ) →
      IsConnected (interior (η '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ a b : ℝ, a < b → IsConnected (interior (η '' Icc a b)) ∧
      closure (interior (η '' Icc a b)) = η '' Icc a b := by
  intro a b hab
  apply connected_interior_image_of_rational_subsegments η hη hab
  · intro p q _ hpq _
    exact hconn p q hpq
  · intro p q _ hpq _
    exact closure_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hpq

end LatticeProb
