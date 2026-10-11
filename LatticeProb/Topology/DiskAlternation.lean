/-
# Alternation of compact connected continua in the round disk

Reduce the two arbitrary compact connected continua to the produced disjoint
finite polygonal arcs at their original circle endpoints. Prune the first
finite chain, preserving strict nonendpoint interior. The original-circle
endpoint parity jump for that chain contradicts the avoiding second disk path.
-/
import LatticeProb.Topology.DiskContinuaArcs
import LatticeProb.Topology.DiskPolygonalAlternation



namespace LatticeProb.Topology
open Set LatticeProb.Topology LatticeProb.Topology.PolygonalParity

/-- **Disk alternation.** Disjoint compact connected subsets of the original
round coordinate disk cannot contain alternating unit-circle endpoints. No
path-connectedness assumption on either continuum is required. -/
theorem disk_alternation_impossible (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hKL : Disjoint K L)
    (h₁ : (Real.cos θ₁, Real.sin θ₁) ∈ K) (h₃ : (Real.cos θ₃, Real.sin θ₃) ∈ K)
    (h₂ : (Real.cos θ₂, Real.sin θ₂) ∈ L) (h₄ : (Real.cos θ₄, Real.sin θ₄) ∈ L) : False := by
  obtain ⟨us, _, hu, _, uh, ul, _, _, p, q, _, _, hpr, _, hsep, hpD, hqD, hpI, _⟩ :=
    disk_continua_have_disjoint_injective_polygonal_arcs θ₁ θ₂ θ₃ θ₄
      h₁₂ h₂₃ h₃₄ h₄₁ K L hK hKc hL hLc hKd hLd hKL h₁ h₃ h₂ h₄
  obtain ⟨vs, hv, hs, vh, vl, hsub⟩ := exists_simple_polygonal_chain us hu
  have hvp : polygonalChain vs ⊆ range p := hsub.trans (le_of_eq hpr.symm)
  exact disk_polygonal_alternation_impossible_internal θ₁ θ₂ θ₃ θ₄ h₁₂ h₂₃ h₃₄ h₄₁
    vs hv hs (vh.trans uh) (vl.trans ul) (hvp.trans hpD)
    (fun _ hz => hpI ⟨hvp hz.1, hz.2⟩) q hqD (hsep.mono_left hvp)

end LatticeProb.Topology
