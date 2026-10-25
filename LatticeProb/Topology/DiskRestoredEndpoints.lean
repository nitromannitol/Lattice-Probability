module

/-
# Original boundary endpoint chains on the actual coordinate disk

This construction uses arbitrary compact connected continua and the original
ordered angles. It supplies finite chains and their exact circle traces.
-/
public import LatticeProb.Topology.DiskEndpointRestoration
public import LatticeProb.Topology.PolygonalChainPlane
public import LatticeProb.Topology.CircleAngleWindow

@[expose] public section



open Metric Set LatticeProb.Topology

namespace LatticeProb.Topology

/-- Containment in the open disk away from two present circle points identifies
the complete circle trace. -/
theorem inter_circle_eq_pair {A : Set (ℝ × ℝ)} {a b : ℝ × ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (haC : a ∈ {z | z.1 ^ 2 + z.2 ^ 2 = 1}) (hbC : b ∈ {z | z.1 ^ 2 + z.2 ^ 2 = 1})
    (hI : A \ {a, b} ⊆ {z | z.1 ^ 2 + z.2 ^ 2 < 1}) :
    A ∩ {z | z.1 ^ 2 + z.2 ^ 2 = 1} = {a, b} := by
  ext z
  constructor
  · rintro ⟨hzA, hzC⟩
    by_contra hne
    have hlt := hI ⟨hzA, hne⟩
    change z.1 ^ 2 + z.2 ^ 2 = 1 at hzC
    change z.1 ^ 2 + z.2 ^ 2 < 1 at hlt
    linarith
  · intro hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact ⟨ha, haC⟩
    · have hzb : z = b := mem_singleton_iff.mp hz
      exact hzb ▸ ⟨hb, hbC⟩

/-- **Disk Restored Endpoints.** The original alternating endpoint data yield finite disjoint chains on the
literal coordinate disk, with only their respective original endpoints on its circle. -/
theorem disk_continua_have_disjoint_restored_endpoint_chains (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hKL : Disjoint K L)
    (h₁ : (Real.cos θ₁, Real.sin θ₁) ∈ K) (h₃ : (Real.cos θ₃, Real.sin θ₃) ∈ K)
    (h₂ : (Real.cos θ₂, Real.sin θ₂) ∈ L) (h₄ : (Real.cos θ₄, Real.sin θ₄) ∈ L) :
    ∃ δ > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 - ρ < δ ∧
      Disjoint (thickening δ K) (thickening δ L) ∧
      ∃ vs ws : List (ℝ × ℝ), ∃ hv : vs ≠ [], ∃ hw : ws ≠ [],
      vs.head hv = (Real.cos θ₁, Real.sin θ₁) ∧
      vs.getLast hv = (Real.cos θ₃, Real.sin θ₃) ∧
      ws.head hw = (Real.cos θ₂, Real.sin θ₂) ∧
      ws.getLast hw = (Real.cos θ₄, Real.sin θ₄) ∧
      polygonalChain vs ⊆ thickening δ K ∧ polygonalChain ws ⊆ thickening δ L ∧
      Disjoint (polygonalChain vs) (polygonalChain ws) ∧
      polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧ polygonalChain ws ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
      polygonalChain vs \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
        {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      polygonalChain ws \ {(Real.cos θ₂, Real.sin θ₂), (Real.cos θ₄, Real.sin θ₄)} ⊆
        {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
      IsCompact (polygonalChain vs) ∧ IsConnected (polygonalChain vs) ∧
      IsCompact (polygonalChain ws) ∧ IsConnected (polygonalChain ws) ∧
      polygonalChain vs ∩ {z | z.1 ^ 2 + z.2 ^ 2 = 1} =
        {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ∧
      polygonalChain ws ∩ {z | z.1 ^ 2 + z.2 ^ 2 = 1} =
        {(Real.cos θ₂, Real.sin θ₂), (Real.cos θ₄, Real.sin θ₄)} ∧
      LatticeProb.IsPolygonal
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm '' polygonalChain vs) ∧
      LatticeProb.IsPolygonal
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm '' polygonalChain ws) ∧
      ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₂, Real.sin θ₂) ∧
      ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₃, Real.sin θ₃) ∧
      ((Real.cos θ₁, Real.sin θ₁) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) ∧
      ((Real.cos θ₂, Real.sin θ₂) : ℝ × ℝ) ≠ (Real.cos θ₃, Real.sin θ₃) ∧
      ((Real.cos θ₂, Real.sin θ₂) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) ∧
      ((Real.cos θ₃, Real.sin θ₃) : ℝ × ℝ) ≠ (Real.cos θ₄, Real.sin θ₄) := by
  obtain ⟨δ, hδ, ρ, hρ0, hρ1, hshort, hsep, vs, ws, hv, hw,
      hhead, hlast, whead, wlast, hvn, hwn, hvD, hwD, hvI, hwI, hdisj⟩ :=
    exists_disjoint_polygonal_chains_with_original_endpoints hK hKc hL hLc hKL
      hKd hLd h₁ h₃ h₂ h₄
      (Real.cos_sq_add_sin_sq θ₁) (Real.cos_sq_add_sin_sq θ₃)
      (Real.cos_sq_add_sin_sq θ₂) (Real.cos_sq_add_sin_sq θ₄)
  have ha : (Real.cos θ₁, Real.sin θ₁) ∈ polygonalChain vs :=
    hhead ▸ head_mem_polygonal_chain hv
  have hb : (Real.cos θ₃, Real.sin θ₃) ∈ polygonalChain vs :=
    hlast ▸ getLast_mem_polygonal_chain hv
  have hc : (Real.cos θ₂, Real.sin θ₂) ∈ polygonalChain ws :=
    whead ▸ head_mem_polygonal_chain hw
  have hd : (Real.cos θ₄, Real.sin θ₄) ∈ polygonalChain ws :=
    wlast ▸ getLast_mem_polygonal_chain hw
  refine ⟨δ, hδ, ρ, hρ0, hρ1, hshort, hsep, vs, ws, hv, hw,
    hhead, hlast, whead, wlast, hvn, hwn, hdisj, hvD, hwD, hvI, hwI,
    isCompact_polygonal_chain vs, isConnected_polygonal_chain hv,
    isCompact_polygonal_chain ws, isConnected_polygonal_chain hw, ?_, ?_, ?_, ?_, ?_⟩
  · exact inter_circle_eq_pair ha hb (Real.cos_sq_add_sin_sq θ₁) (Real.cos_sq_add_sin_sq θ₃) hvI
  · exact inter_circle_eq_pair hc hd (Real.cos_sq_add_sin_sq θ₂) (Real.cos_sq_add_sin_sq θ₄) hwI
  · exact isPolygonal_image_polygonal_chain
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toLinearMap vs
  · exact isPolygonal_image_polygonal_chain
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toLinearMap ws
  · exact circle_points_pairwise_ne_of_cyclic_order h₁₂ h₂₃ h₃₄ h₄₁

end LatticeProb.Topology
