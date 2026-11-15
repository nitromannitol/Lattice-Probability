import LatticeProb.Analysis.WedgeArcSineCoreSymmetry
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # Closability of the angular sine core -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A symmetric operator whose domain has trivial orthogonal complement is closable. -/
theorem symmetric_linearPMap_isClosable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →ₗ.[ℂ] E)
    (hdense : T.domainᗮ = ⊥)
    (hsym : ∀ u v : T.domain, inner ℂ (T u) (v : E) = inner ℂ (u : E) (T v)) :
    T.IsClosable := by
  let G := T.graph.topologicalClosure
  have hgraph : ∀ p : E × E, p ∈ G → p.1 = 0 → p.2 = 0 := by
    intro p hp hp0
    have horth : p.2 ∈ T.domainᗮ := by
      apply (Submodule.mem_orthogonal' T.domain p.2).2
      intro x hx
      have hclosed : IsClosed {q : E × E | inner ℂ q.2 x = inner ℂ q.1 (T ⟨x, hx⟩)} :=
        isClosed_eq (by fun_prop) (by fun_prop)
      have hsub : (T.graph : Set (E × E)) ⊆
          {q : E × E | inner ℂ q.2 x = inner ℂ q.1 (T ⟨x, hx⟩)} := by
        intro q hq
        rcases (LinearPMap.mem_graph_iff T).mp hq with ⟨u, hu, hv⟩
        change inner ℂ q.2 x = inner ℂ q.1 (T ⟨x, hx⟩)
        rw [← hu, ← hv]
        exact hsym u ⟨x, hx⟩
      have h := closure_minimal hsub hclosed hp
      change inner ℂ p.2 x = inner ℂ p.1 (T ⟨x, hx⟩) at h
      simpa [hp0] using h
    rw [hdense, Submodule.mem_bot] at horth
    exact horth
  refine ⟨G.toLinearPMap, ?_⟩
  exact (Submodule.toLinearPMap_graph_eq G hgraph).symm

/-- The finite angular sine core, viewed as a partially defined operator. -/
noncomputable def wedgeArcSinePMap {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi) :
    Lp ℂ 2 (wedgeArcSurfaceMeasure θ) →ₗ.[ℂ] Lp ℂ 2 (wedgeArcSurfaceMeasure θ) :=
  ⟨_, wedgeArcSineCore hθ hθ'⟩

/-- The finite angular sine core has a closed extension. -/
theorem wedgeArcSinePMap_isClosable {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) : (wedgeArcSinePMap hθ hθ').IsClosable := by
  apply symmetric_linearPMap_isClosable
  · exact wedgeArcSineLp_orthogonal_eq_bot hθ hθ'
  · exact wedgeArcSineCore_symmetric hθ hθ'

end LatticeProb
