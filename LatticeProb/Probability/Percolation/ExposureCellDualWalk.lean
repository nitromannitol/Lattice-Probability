import LatticeProb.Probability.Percolation.VerticalExposureCells

/-!
# Dual walks in exposure cells

Each face of an attained exposure region can be joined to a bottom face by a
dual-open walk contained in that region.
-/

open Percolation.Literature

namespace EdgeCrossing

/-- Every face in an attained exposure region has a dual-open walk to its bottom side. -/
theorem exists_dualWalk_of_mem_verticalExposureCell (n : ℕ)
    (D : Finset (LatticeModels.Site 2))
    (η : (LatticeModels.zdGraph 2).edgeSet → Prop)
    (hη : η ∈ verticalExposureCell n D) {f : LatticeModels.Site 2} (hf : f ∈ D) :
    ∃ b ∈ dualBottomSide n n, ∃ q : (LatticeModels.zdGraph 2).Walk f b,
      (∀ z ∈ q.support, z ∈ D) ∧
      ∀ e ∈ q.edges, e ∈ dualConfig (BondConfig.relabel
        (sym2Equiv (exposureRotation n).toEquiv) (extend (LatticeModels.zdGraph 2) η)) := by
  have hach : dualBelow n (BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
      (extend (LatticeModels.zdGraph 2) η)) = D := hη
  have hf' : f ∈ dualBelow n (BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
      (extend (LatticeModels.zdGraph 2) η)) := hach.symm ▸ hf
  obtain ⟨b, hb, hconn⟩ := exists_openConnIn_dualBelow hf'
  obtain ⟨q, hqS, hqω⟩ := exists_walk_of_mem_openConnIn
    (fun _ h => h.1 : dualConfig (BondConfig.relabel
      (sym2Equiv (exposureRotation n).toEquiv) (extend (LatticeModels.zdGraph 2) η)) ⊆
        (LatticeModels.zdGraph 2).edgeSet) hconn
  refine ⟨b, hb, q.reverse, ?_, ?_⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hach ▸ hqS z hz
  · intro e he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact hqω e he

end EdgeCrossing
