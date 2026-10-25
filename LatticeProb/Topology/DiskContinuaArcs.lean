module

/-
# Polygonal arcs from disjoint compact disk continua

Restore the four prescribed circle endpoints after inward scaling and polygonal
approximation in separated connected neighborhoods. Finite loop pruning then
produces two disjoint injective paths, with the same original endpoints and
strictly interior nonendpoint points, from arbitrary compact connected continua.
-/
public import LatticeProb.Topology.DiskArcPair
public import LatticeProb.Topology.DiskRestoredEndpoints

@[expose] public section

open Set LatticeProb.Topology

namespace LatticeProb.Topology

/-- **Disk Continua Arcs.** Compact connected disk continua with alternating endpoints yield disjoint injective polygonal crosscuts. -/
theorem disk_continua_have_disjoint_injective_polygonal_arcs (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (K L : Set (ℝ × ℝ)) (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hKL : Disjoint K L)
    (h₁ : (Real.cos θ₁, Real.sin θ₁) ∈ K) (h₃ : (Real.cos θ₃, Real.sin θ₃) ∈ K)
    (h₂ : (Real.cos θ₂, Real.sin θ₂) ∈ L) (h₄ : (Real.cos θ₄, Real.sin θ₄) ∈ L) :
    ∃ us zs : List (ℝ × ℝ), ∃ hu : us ≠ [], ∃ hz : zs ≠ [],
      us.head hu = (Real.cos θ₁, Real.sin θ₁) ∧
      us.getLast hu = (Real.cos θ₃, Real.sin θ₃) ∧
      zs.head hz = (Real.cos θ₂, Real.sin θ₂) ∧
      zs.getLast hz = (Real.cos θ₄, Real.sin θ₄) ∧
      ∃ p : Path (Real.cos θ₁, Real.sin θ₁) (Real.cos θ₃, Real.sin θ₃),
      ∃ q : Path (Real.cos θ₂, Real.sin θ₂) (Real.cos θ₄, Real.sin θ₄),
        Function.Injective p ∧ Function.Injective q ∧
        range p = polygonalChain us ∧ range q = polygonalChain zs ∧
        Disjoint (range p) (range q) ∧ range p ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧ range q ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1} ∧
        range p \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
          {z | z.1 ^ 2 + z.2 ^ 2 < 1} ∧
        range q \ {(Real.cos θ₂, Real.sin θ₂), (Real.cos θ₄, Real.sin θ₄)} ⊆
          {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
  obtain ⟨_, _, _, _, _, _, _, vs, ws, hv, hw, hhead, hlast, whead, wlast,
      _, _, hdisj, hvD, hwD, hvI, hwI, _⟩ :=
    disk_continua_have_disjoint_restored_endpoint_chains θ₁ θ₂ θ₃ θ₄
      h₁₂ h₂₃ h₃₄ h₄₁ K L hK hKc hL hLc hKd hLd hKL h₁ h₃ h₂ h₄
  have hd := circle_points_pairwise_ne_of_cyclic_order h₁₂ h₂₃ h₃₄ h₄₁
  have hvne : vs.head hv ≠ vs.getLast hv := by
    rw [hhead, hlast]
    exact hd.2.1
  have hwne : ws.head hw ≠ ws.getLast hw := by
    rw [whead, wlast]
    exact hd.2.2.2.2.1
  have hvI' : polygonalChain vs \ {vs.head hv, vs.getLast hv} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
    simpa only [hhead, hlast] using hvI
  have hwI' : polygonalChain ws \ {ws.head hw, ws.getLast hw} ⊆
      {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
    simpa only [whead, wlast] using hwI
  have arcs := DiskArcPair.disjoint_disk_chain_pair_consumer
    hv hw hvne hwne hdisj hvD hwD hvI' hwI'
  obtain ⟨us, zs, hu, hz, uh, ul, zh, zl, p, q, hp, hq, hpr, hqr,
      hsep, hpD, hqD, hpI, hqI⟩ := arcs
  exact ⟨us, zs, hu, hz, uh.trans hhead, ul.trans hlast,
    zh.trans whead, zl.trans wlast,
    p.cast hhead.symm hlast.symm, q.cast whead.symm wlast.symm,
    hp, hq, hpr, hqr, hsep, hpD, hqD,
    fun _ h => hpI ⟨h.1, by simpa only [hhead, hlast] using h.2⟩,
    fun _ h => hqI ⟨h.1, by simpa only [whead, wlast] using h.2⟩⟩

end LatticeProb.Topology
