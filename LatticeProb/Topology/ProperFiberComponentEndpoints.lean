import LatticeProb.Topology.ProperFiberComponentTransfer
import LatticeProb.Topology.AreaCurveIntervalContainment
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Component interval endpoints for curves with equal fibres -/

set_option autoImplicit false

open Function MeasureTheory Set Topology

namespace LatticeProb

/-- Nondegenerate component interval witnesses have the same endpoints when
proper surjections have equal fibres and one curve is area-parametrized. -/
theorem endpoints_eq_of_proper_maps_same_fibers_components
    {Y : Type*} [TopologicalSpace Y]
    (g : ℝ → Y) (η : ℝ → ℂ) (μ : Measure ℂ)
    (hg : IsProperMap g) (hη : IsProperMap η)
    (hgs : Surjective g) (hηs : Surjective η)
    (hfg : ∀ v w, g v = g w ↔ η v = η w)
    (harea : ∀ v w, v < w → μ (η '' Icc v w) = ENNReal.ofReal (w - v))
    (s t u a b c d : ℝ)
    (hu : g u ∈ interior (g '' Icc s t))
    (hab : a < b) (hcd : c < d)
    (hgcomp : g '' Icc a b =
      closure (connectedComponentIn (interior (g '' Icc s t)) (g u)))
    (hηcomp : η '' Icc c d =
      closure (connectedComponentIn (interior (η '' Icc s t)) (η u))) :
    a = c ∧ b = d := by
  have htransfer := image_eq_componentClosure_of_proper_maps_same_fibers
    g η hg hη hgs hηs hfg (Icc s t) (Icc a b) u hu hgcomp
  exact endpoints_eq_of_area_curve_image_eq η μ hη.continuous harea hab hcd
    (htransfer.trans hηcomp.symm)

end LatticeProb
