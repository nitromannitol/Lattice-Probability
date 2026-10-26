import LatticeProb.Prob.Percolation.RootedCorrectedPlaneBorel

/-!
# Unique ambient encoding of a normalized source plane

A unique normalized corrected plane on an actual root component has a unique ambient
coordinate encoding that is zero outside that component. The source object remains a
function on the component; the extension is constructed only inside the existence proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- Existence and uniqueness on the actual component give existence and uniqueness of
its ambient encoding, with normalization and the complete outside-zero clause. -/
theorem existsUnique_rooted_encoded_correctedPlane (ω : Configuration d) (o : Vertex d)
    (q : Fin d → ℝ)
    (h : ∃! u : (openGraph ω).connectedComponentMk o → ℝ,
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q u ∧
        u ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ = 0) :
    ∃! U : Vertex d → ℝ, U o = 0 ∧
      IsCorrectedPlane ((openGraph ω).connectedComponentMk o) q (fun x => U x.val) ∧
      ∀ x, ¬ (openGraph ω).Reachable o x → U x = 0 := by
  classical
  let C := (openGraph ω).connectedComponentMk o
  obtain ⟨u, ⟨hu, hnorm⟩, hunique⟩ := h
  let U : Vertex d → ℝ := fun x => if hx : x ∈ C.supp then u ⟨x, hx⟩ else 0
  have hrestrict : (fun x : C => U x.val) = u := by
    funext x
    exact dif_pos x.property
  have hroot : U o = 0 := by
    rw [show U o = u ⟨o, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ from
      dif_pos SimpleGraph.ConnectedComponent.connectedComponentMk_mem]
    exact hnorm
  have hout : ∀ x, ¬ (openGraph ω).Reachable o x → U x = 0 := by
    intro x hx
    apply dif_neg
    intro hm
    exact hx (C.reachable_of_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hm)
  refine ⟨U, ⟨hroot, ?_, hout⟩, ?_⟩
  · change IsCorrectedPlane C q (fun x => U x.val)
    rw [hrestrict]
    exact hu
  · intro V hV
    have heq : (fun x : C => V x.val) = u := hunique _ ⟨hV.2.1, hV.1⟩
    funext x
    by_cases hx : x ∈ C.supp
    · have hv := congrFun heq ⟨x, hx⟩
      rw [show U x = u ⟨x, hx⟩ from dif_pos hx]
      exact hv
    · have hr : ¬ (openGraph ω).Reachable o x := by
        intro hr
        exact hx ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
          (SimpleGraph.ConnectedComponent.sound hr.symm))
      exact (hV.2.2 x hr).trans (hout x hr).symm

end LatticeProb.Percolation
