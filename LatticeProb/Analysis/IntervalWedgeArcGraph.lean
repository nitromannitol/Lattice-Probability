import LatticeProb.Analysis.IntervalWedgeArcSineIsometry
import LatticeProb.Analysis.WedgeArcSineClosureSpecialization
import LatticeProb.Analysis.ClassicalIntervalGradientSelfAdjoint

/-! # Transport of the interval gradient composition to a circular arc -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The sine-core graph on an arc corresponds, under the sine isometry, to
    the graph of the closed interval gradient followed by its adjoint. -/
theorem intervalWedgeArcSineIsometry_graph_iff {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (x y : Lp ℂ 2 (volume.restrict (Ioo (-θ / 2) (θ / 2)))) :
    (intervalWedgeArcSineIsometry hθ hθ' x,
      intervalWedgeArcSineIsometry hθ hθ' y) ∈
        (wedgeArcSinePMap hθ hθ').graph.topologicalClosure ↔
    (x, y) ∈ (classicalIntervalGradientComposition (-θ / 2) (θ / 2)).graph := by
  have hab : -θ / 2 < θ / 2 := by linarith
  rw [wedgeArcSinePMap_graph_closure_iff hθ hθ',
    classicalIntervalGradientComposition_eq_sine_adjoint hab,
    hilbertBasis_diagonal_adjoint_graph_eq_closure,
    hilbertBasis_diagonal_graph_closure_iff]
  have hlen : θ / 2 - -θ / 2 = θ := by ring
  simp only [hlen, intervalSineHilbertBasis_apply]
  constructor <;> intro h n
  · simpa only [← intervalWedgeArcSineIsometry_apply_mode hθ hθ' n,
      LinearIsometryEquiv.inner_map_map] using h n
  · simpa only [← intervalWedgeArcSineIsometry_apply_mode hθ hθ' n,
      LinearIsometryEquiv.inner_map_map] using h n

end LatticeProb
