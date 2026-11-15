import LatticeProb.Analysis.WedgeArcSineAdjoint

/-! # Closed symmetric extensions of the angular sine core -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A closed symmetric partial operator extending the finite angular sine core
has exactly the closed sine graph. -/
theorem wedgeArcSinePMap_closed_symmetric_extension_graph {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (A : Lp ℂ 2 (wedgeArcSurfaceMeasure θ) →ₗ.[ℂ]
      Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
    (hclosed : IsClosed (A.graph : Set (Lp ℂ 2 (wedgeArcSurfaceMeasure θ) ×
      Lp ℂ 2 (wedgeArcSurfaceMeasure θ))))
    (hext : (wedgeArcSinePMap hθ hθ').graph ≤ A.graph)
    (hsymm : ∀ p ∈ A.graph, ∀ q ∈ A.graph,
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1) :
    A.graph = (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := by
  apply le_antisymm
  · intro p hp
    apply (wedgeArcSinePMap_graph_closure_iff_core_pairing hθ hθ' p.1 p.2).2
    intro v
    apply hsymm _ (hext (LinearPMap.mem_graph (wedgeArcSinePMap hθ hθ') v)) _ hp
  · intro p hp
    exact closure_minimal (fun _ hx => hext hx) hclosed hp

end LatticeProb
