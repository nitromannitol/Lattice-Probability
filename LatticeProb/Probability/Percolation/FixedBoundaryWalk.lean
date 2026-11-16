import LatticeProb.Probability.Percolation.ExposureComponentSeparation
import LatticeProb.Probability.Percolation.BoundaryRotationTransport

/-!
# Fixed boundary walks for exposure cells

An indexed dual region determines a boundary walk before a configuration in its
exposure cell is selected. The walk is open throughout the cell and its
first-contact component avoids the exposed faces and edges.
-/

open Percolation.Literature SimpleGraph

namespace EdgeCrossing

/-- An indexed exposure region admits one physical boundary walk with the same
open-edge and first-contact separation properties throughout its exposure cell. -/
theorem exists_fixed_boundaryWalk (n : ℕ) (hn : 1 ≤ n)
    (D : Finset (LatticeModels.Site 2)) (hD : D ∈ verticalExposureIndices n) :
    ∃ c d : LatticeModels.Site 2, ∃ Q : (LatticeModels.zdGraph 2).Walk c d,
      c 1 = 0 ∧ d 1 = n ∧
      (∀ z ∈ Q.support, z ∈ rectangle n n) ∧
      (∀ e ∈ Q.darts,
        IsBdryEdge D n s(exposureRotation n e.fst, exposureRotation n e.snd)) ∧
      ∀ η ∈ verticalExposureCell n D,
        (∀ x y, s(x, y) ∈ Q.edges →
          s(exposureRotation n x, exposureRotation n y) ∈
            BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
              (extend (LatticeModels.zdGraph 2) η)) ∧
        (∀ (v : LatticeModels.Site 2) (e : Sym2 (LatticeModels.Site 2)),
          e ∈ belowEdges D → exposureRotation n v ∈ e →
            v ∉ firstContactComponent n Q) ∧
        (∀ (f v : LatticeModels.Site 2) (e : Sym2 (LatticeModels.Site 2)),
          f ∈ D → e ∈ squareEdges f → exposureRotation n v ∈ e →
            v ∉ firstContactComponent n Q) ∧
        ∀ f v : LatticeModels.Site 2, f ∈ D →
          (exposureRotation n v 0 = f 0 ∨ exposureRotation n v 0 = f 0 + 1) →
          (exposureRotation n v 1 = f 1 ∨ exposureRotation n v 1 = f 1 + 1) →
            v ∉ firstContactComponent n Q := by
  obtain ⟨_, hbot, htop⟩ := Finset.mem_filter.mp hD
  obtain ⟨a, b, ha, hb, π, hπ, hbdry⟩ := exists_bdryWalk hbot htop
  let r := exposureRotation n
  let Q := π.map r.symm.toEmbedding.toHom
  have hrot := inverseRotated_boundaryWalk n D π ha hb hπ hbdry
  change (r.symm a) 1 = 0 ∧ (r.symm b) 1 = n ∧
    (∀ z ∈ Q.support, z ∈ rectangle n n) ∧
    (∀ x y, s(x, y) ∈ Q.edges → s(r x, r y) ∈ π.edges) ∧
    ∀ η ∈ verticalExposureCell n D, ∀ x y, s(x, y) ∈ Q.edges →
      s(r x, r y) ∈ BondConfig.relabel (sym2Equiv r.toEquiv)
        (extend (LatticeModels.zdGraph 2) η) at hrot
  have hQbdry : ∀ e ∈ Q.darts, IsBdryEdge D n s(r e.fst, r e.snd) := by
    intro e he
    simp only [Q, Walk.darts_map, List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    simpa [r, Dart.edge] using hbdry e he
  refine ⟨r.symm a, r.symm b, Q, hrot.1, hrot.2.1, hrot.2.2.1, hQbdry, ?_⟩
  intro η hη
  refine ⟨hrot.2.2.2.2 η hη, ?_, ?_, ?_⟩
  · intro v e he hv
    exact not_mem_firstContactComponent_of_rotated_boundary n hn D hD Q hrot.1 hrot.2.1
      hrot.2.2.1 hQbdry η hη he hv
  · intro f v e hf he hv
    apply not_mem_firstContactComponent_of_rotated_boundary n hn D hD Q hrot.1 hrot.2.1
      hrot.2.2.1 hQbdry η hη _ hv
    exact Finset.mem_biUnion.mpr ⟨f, hf, he⟩
  · intro f v hf h₀ h₁
    exact not_mem_firstContactComponent_of_rotated_face n hn D hD Q hrot.1 hrot.2.1
      hrot.2.2.1 hQbdry η hη hf h₀ h₁

end EdgeCrossing
