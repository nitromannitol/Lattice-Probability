import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Weak equations and adjoints of partial operators -/

set_option autoImplicit false

namespace LatticeProb

/-- A weak energy identity on the entire domain of a densely defined operator
identifies the adjoint applied to the image of each core element. -/
theorem adjoint_apply_of_weak_energy_identity {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (G : E →ₗ.[ℂ] F) (C : E →ₗ.[ℂ] E)
    (hdense : Dense (G.domain : Set E)) (hdom : C.domain ≤ G.domain)
    (hweak : ∀ (u : C.domain) (v : G.domain),
      inner ℂ (C u) (v : E) = inner ℂ (G ⟨u, hdom u.property⟩) (G v))
    (u : C.domain) :
    ∃ h : G ⟨u, hdom u.property⟩ ∈ G.adjoint.domain,
      G.adjoint ⟨G ⟨u, hdom u.property⟩, h⟩ = C u := by
  have hmem : G ⟨u, hdom u.property⟩ ∈ G.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨C u, hweak u⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq hdense _ (hweak u)⟩

end LatticeProb
