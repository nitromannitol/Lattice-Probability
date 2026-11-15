import LatticeProb.Analysis.WedgeArcSineAdjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Adjoint graph of the angular sine core -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The adjoint of the finite angular sine core has exactly the graph closure
of the core. -/
theorem wedgeArcSinePMap_adjoint_graph_eq_closure {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    (wedgeArcSinePMap hθ hθ').adjoint.graph =
      (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := by
  have hd : Dense ((wedgeArcSinePMap hθ hθ').domain : Set
      (Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact wedgeArcSineCore_dense hθ hθ'
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rw [Submodule.mem_adjoint_iff,
    wedgeArcSinePMap_graph_closure_iff_core_pairing hθ hθ' p.1 p.2]
  constructor
  · intro h v
    have hmem : ((v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)),
        wedgeArcSineCore hθ hθ' v) ∈ (wedgeArcSinePMap hθ hθ').graph := by
      exact LinearPMap.mem_graph (wedgeArcSinePMap hθ hθ') v
    have hv := h (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
      (wedgeArcSineCore hθ hθ' v) hmem
    exact (sub_eq_zero.mp hv).symm
  · intro h a b hab
    obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff _).mp hab
    change (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) = a at hv
    change wedgeArcSineCore hθ hθ' v = b at hw
    rw [← hv, ← hw]
    exact sub_eq_zero.mpr (h v).symm

end LatticeProb
