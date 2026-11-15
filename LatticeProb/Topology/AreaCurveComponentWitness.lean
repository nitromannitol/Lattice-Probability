import LatticeProb.Topology.AreaCurveRegularClosed
import LatticeProb.Topology.AreaCurveIntervalContainment
import LatticeProb.Topology.CurveComponentRegularOpen

/-! # Component witnesses for area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- A nondegenerate interval witnesses the closure of an interior component
exactly when its image interior is that component. -/
theorem image_Icc_eq_closure_component_iff_interior_eq
    (η : ℝ → ℂ) (μ : Measure ℂ) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {K : Set ℂ} (hK : IsClosed K) (x : ℂ) {a b : ℝ} (hab : a < b) :
    η '' Icc a b = closure (connectedComponentIn (interior K) x) ↔
      interior (η '' Icc a b) = connectedComponentIn (interior K) x := by
  constructor
  · exact interior_image_eq_component_of_image_eq_closure η _ hK x
  · intro h
    calc
      η '' Icc a b = closure (interior (η '' Icc a b)) :=
        (closure_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hab).symm
      _ = closure (connectedComponentIn (interior K) x) := congrArg closure h

/-- Nondegenerate interval images with equal interiors have equal endpoints. -/
theorem endpoints_eq_of_proper_area_curve_interior_image_eq
    (η : ℝ → ℂ) (μ : Measure ℂ) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (heq : interior (η '' Icc a b) = interior (η '' Icc c d)) :
    a = c ∧ b = d := by
  apply endpoints_eq_of_area_curve_image_eq η μ hη harea hab hcd
  calc
    η '' Icc a b = closure (interior (η '' Icc a b)) :=
      (closure_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hab).symm
    _ = closure (interior (η '' Icc c d)) := congrArg closure heq
    _ = η '' Icc c d :=
      closure_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hcd

end LatticeProb
