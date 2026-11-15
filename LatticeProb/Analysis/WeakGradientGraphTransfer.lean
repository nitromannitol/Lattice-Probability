import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Weak identities on operator graph closures -/

set_option autoImplicit false

namespace LatticeProb

/-- A weak pairing identity on a partial operator's graph extends to every
operator whose graph lies in its product-topological closure. -/
theorem weak_pairing_of_graph_subset_closure {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (H G : E →ₗ.[ℂ] F) (a : E) (b : F)
    (hgraph : G.graph ≤ H.graph.topologicalClosure)
    (hweak : ∀ v : H.domain, inner ℂ a (v : E) = inner ℂ b (H v))
    (v : G.domain) : inner ℂ a (v : E) = inner ℂ b (G v) := by
  have hclosed : IsClosed {p : E × F | inner ℂ a p.1 = inner ℂ b p.2} :=
    isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
  have hbase : (H.graph : Set (E × F)) ⊆
      {p : E × F | inner ℂ a p.1 = inner ℂ b p.2} := by
    intro p hp
    obtain ⟨w, hw, hw'⟩ := (LinearPMap.mem_graph_iff H).mp hp
    change (w : E) = p.1 at hw
    change H w = p.2 at hw'
    change inner ℂ a p.1 = inner ℂ b p.2
    simpa only [← hw, ← hw'] using hweak w
  have hclosure := closure_minimal hbase hclosed
  have hv := hgraph (LinearPMap.mem_graph G v)
  exact hclosure hv

end LatticeProb
