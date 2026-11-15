import LatticeProb.Analysis.WedgeArcSineClosureSpecialization

/-! # Weak pairing characterization of the angular sine operator -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The closed angular sine graph consists exactly of pairs satisfying the
weak equation against every finite sine-core test. -/
theorem wedgeArcSinePMap_graph_closure_iff_core_pairing {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    (x y : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) :
    (x, y) ∈ (wedgeArcSinePMap hθ hθ').graph.topologicalClosure ↔
      ∀ v : Submodule.span ℂ (Set.range (wedgeArcSineLp θ)),
        inner ℂ (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) y =
          inner ℂ (wedgeArcSineCore hθ hθ' v) x := by
  constructor
  · intro h v
    have hclosed : IsClosed {p : Lp ℂ 2 (wedgeArcSurfaceMeasure θ) ×
        Lp ℂ 2 (wedgeArcSurfaceMeasure θ) |
        inner ℂ (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) p.2 =
          inner ℂ (wedgeArcSineCore hθ hθ' v) p.1} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : ((wedgeArcSinePMap hθ hθ').graph : Set
        (Lp ℂ 2 (wedgeArcSurfaceMeasure θ) × Lp ℂ 2 (wedgeArcSurfaceMeasure θ))) ⊆
        {p | inner ℂ (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) p.2 =
          inner ℂ (wedgeArcSineCore hθ hθ' v) p.1} := by
      intro p hp
      obtain ⟨u, hu, hv⟩ := (LinearPMap.mem_graph_iff (wedgeArcSinePMap hθ hθ')).mp hp
      change inner ℂ (v : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) p.2 =
        inner ℂ (wedgeArcSineCore hθ hθ' v) p.1
      rw [← hu, ← hv]
      exact (wedgeArcSineCore_symmetric hθ hθ' v u).symm
    exact closure_minimal hsub hclosed h
  · intro h
    apply (wedgeArcSinePMap_graph_closure_iff hθ hθ' x y).2
    intro n
    have hv := h ⟨wedgeArcSineLp θ n, Submodule.subset_span ⟨n, rfl⟩⟩
    rw [wedgeArcSineCore_apply_mode, inner_smul_left] at hv
    simpa only [Complex.conj_ofReal] using hv

end LatticeProb
