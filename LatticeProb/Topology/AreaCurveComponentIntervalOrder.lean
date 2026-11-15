import LatticeProb.Topology.ComponentIntervalOrder
import LatticeProb.Topology.ProperAreaCurveFrontier
import LatticeProb.Topology.CurveComponentFrontier
import Mathlib.Topology.Connected.LocallyConnected

/-! # Intervals of components of area-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- If distinct interior components of a proper area-parametrized planar curve
segment have interval images as their closures, those intervals are ordered. -/
theorem component_interval_order_of_proper_area_curve
    (η : ℝ → ℂ) (μ : Measure ℂ) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η)
    (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t a b c d : ℝ} (hst : s < t) (hab : a < b) (hcd : c < d)
    (x y : ℂ)
    (hne : connectedComponentIn (interior (η '' Icc s t)) x ≠
      connectedComponentIn (interior (η '' Icc s t)) y)
    (hU : η '' Icc a b = closure (connectedComponentIn (interior (η '' Icc s t)) x))
    (hV : η '' Icc c d = closure (connectedComponentIn (interior (η '' Icc s t)) y)) :
    b ≤ c ∨ d ≤ a := by
  let K := η '' Icc s t
  let U := connectedComponentIn (interior K) x
  let V := connectedComponentIn (interior K) y
  have hK : IsClosed K := (isCompact_Icc.image hη).isClosed
  have hfront : μ (frontier K) = 0 :=
    measure_frontier_image_Icc_eq_zero_of_proper η μ hη hp hs harea hst
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    apply hne
    exact (connectedComponentIn_eq hzU).trans (connectedComponentIn_eq hzV).symm
  apply interval_order_of_disjoint_open_curve_regions η μ U V hab hcd hη.measurable hmap hdis
    isOpen_interior.connectedComponentIn isOpen_interior.connectedComponentIn
    (measure_frontier_component_interior_eq_zero hK μ hfront x)
    (measure_frontier_component_interior_eq_zero hK μ hfront y) hU hV
  · rw [harea a b hab, Real.volume_Icc]
  · rw [harea c d hcd, Real.volume_Icc]

end LatticeProb
