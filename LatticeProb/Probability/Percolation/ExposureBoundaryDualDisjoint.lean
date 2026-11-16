import LatticeProb.Probability.Percolation.BoundaryRotationTransport
import LatticeProb.Probability.Percolation.ExposureCellDualWalk
import LatticeProb.Probability.Percolation.OpenRotatedDualDisjoint

/-!
# Boundary and dual walks in an exposure cell

A fixed boundary walk and a dual-open walk in the same exposure configuration
have disjoint physical primal and rotated dual subdivisions.
-/

open Percolation.Literature

namespace EdgeCrossing

/-- A fixed boundary walk avoids every dual-open walk in the same exposure cell. -/
theorem disjoint_boundaryWalk_rotatedDual_of_mem_verticalExposureCell (n : ℕ)
    (D : Finset (LatticeModels.Site 2))
    {a b : LatticeModels.Site 2} (π : (LatticeModels.zdGraph 2).Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge)
    (η : (LatticeModels.zdGraph 2).edgeSet → Prop)
    (hη : η ∈ verticalExposureCell n D)
    {f g : LatticeModels.Site 2} (q : (LatticeModels.zdGraph 2).Walk f g)
    (hq : ∀ e ∈ q.edges, e ∈ dualConfig (BondConfig.relabel
      (sym2Equiv (exposureRotation n).toEquiv) (extend (LatticeModels.zdGraph 2) η))) :
    Disjoint {z | z ∈ (subdivideWalk (π.map
      (exposureRotation n).symm.toEmbedding.toHom)).support}
      {z | z ∈ (subdivideRotatedDualWalk n q).support} := by
  apply disjoint_support_subdivideWalk_rotatedDual_of_open n
    (BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
      (extend (LatticeModels.zdGraph 2) η))
  · exact (inverseRotated_boundaryWalk n D π ha hb hπ hbdry).2.2.2.2 η hη
  · exact fun f g hfg => hq s(f, g) hfg

/-- Each face of the actual exposure region has an avoiding dual walk to the bottom. -/
theorem exists_dualWalk_disjoint_boundaryWalk_of_mem_verticalExposureCell (n : ℕ)
    (D : Finset (LatticeModels.Site 2))
    {a b : LatticeModels.Site 2} (π : (LatticeModels.zdGraph 2).Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge)
    (η : (LatticeModels.zdGraph 2).edgeSet → Prop)
    (hη : η ∈ verticalExposureCell n D) {f : LatticeModels.Site 2} (hf : f ∈ D) :
    ∃ b ∈ dualBottomSide n n, ∃ q : (LatticeModels.zdGraph 2).Walk f b,
      (∀ z ∈ q.support, z ∈ D) ∧
      (∀ e ∈ q.edges, e ∈ dualConfig (BondConfig.relabel
        (sym2Equiv (exposureRotation n).toEquiv) (extend (LatticeModels.zdGraph 2) η))) ∧
      Disjoint {z | z ∈ (subdivideWalk (π.map
        (exposureRotation n).symm.toEmbedding.toHom)).support}
        {z | z ∈ (subdivideRotatedDualWalk n q).support} := by
  obtain ⟨c, hc, q, hs, he⟩ := exists_dualWalk_of_mem_verticalExposureCell n D η hη hf
  exact ⟨c, hc, q, hs, he,
    disjoint_boundaryWalk_rotatedDual_of_mem_verticalExposureCell n D π ha hb hπ hbdry
      η hη q he⟩

end EdgeCrossing
