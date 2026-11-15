import LatticeProb.Analysis.WedgeArcSineAdjointGraph

/-! # Self-adjoint angular sine operator -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The adjoint of the finite angular sine core is self-adjoint. -/
theorem wedgeArcSinePMap_adjoint_isSelfAdjoint {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    IsSelfAdjoint (wedgeArcSinePMap hθ hθ').adjoint := by
  let C := wedgeArcSinePMap hθ hθ'
  let A := C.adjoint
  have hgraph : A.graph = C.graph.topologicalClosure :=
    wedgeArcSinePMap_adjoint_graph_eq_closure hθ hθ'
  have hcore : C.graph ≤ A.graph := by
    rw [hgraph]
    exact Submodule.le_topologicalClosure C.graph
  have hd : Dense (A.domain : Set (Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) := by
    have hc : Dense (C.domain : Set (Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) := by
      apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
      exact wedgeArcSineCore_dense hθ hθ'
    apply hc.mono
    intro x hx
    have hg := hcore (LinearPMap.mem_graph C ⟨x, hx⟩)
    obtain ⟨z, hz, _⟩ := (LinearPMap.mem_graph_iff A).mp hg
    change (z : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) = x at hz
    rw [← hz]
    exact z.property
  have hsymm : ∀ p ∈ A.graph, ∀ q ∈ A.graph,
      inner ℂ p.1 q.2 = inner ℂ p.2 q.1 := by
    intro p hp q hq
    have hp' : ∀ v : C.domain, inner ℂ (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) p.2 =
        inner ℂ (C v) p.1 := by
      apply (wedgeArcSinePMap_graph_closure_iff_core_pairing hθ hθ' p.1 p.2).1
      rw [← hgraph]
      exact hp
    have hclosed : IsClosed {r : Lp ℂ 2 (wedgeArcSurfaceMeasure θ) ×
        Lp ℂ 2 (wedgeArcSurfaceMeasure θ) | inner ℂ p.1 r.2 = inner ℂ p.2 r.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : (C.graph : Set (Lp ℂ 2 (wedgeArcSurfaceMeasure θ) ×
        Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) ⊆
        {r | inner ℂ p.1 r.2 = inner ℂ p.2 r.1} := by
      intro r hr
      obtain ⟨v, hv, hw⟩ := (LinearPMap.mem_graph_iff C).mp hr
      change inner ℂ p.1 r.2 = inner ℂ p.2 r.1
      rw [← hv, ← hw]
      have hh := hp' v
      rw [← inner_conj_symm p.1 (C v),
        ← inner_conj_symm p.2 (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)), hh]
    apply closure_minimal hsub hclosed
    rw [hgraph] at hq
    exact hq
  change IsSelfAdjoint A
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    rw [hgraph]
    apply (wedgeArcSinePMap_graph_closure_iff_core_pairing hθ hθ' p.1 p.2).2
    intro v
    have hh := hp (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) (C v)
      (hcore (LinearPMap.mem_graph C v))
    exact (sub_eq_zero.mp hh).symm
  · intro hp a b hab
    exact sub_eq_zero.mpr (hsymm (a, b) hab p hp).symm

end LatticeProb
