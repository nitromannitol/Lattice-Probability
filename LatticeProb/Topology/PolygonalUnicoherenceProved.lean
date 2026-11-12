/-
Unicoherence of the plane for compact connected sets, and hence the frozen
polygonal statement `LatticeProb.PolygonalUnicoherence`.

The frontier of every component of the complement of a closed connected subset
of `ℂ` is connected (`LatticeProb.Topology.isConnected_frontier_of_mem_connectedComponentsIn_compl`).
The statement is transported to `Plane = Fin 2 → ℝ` along the linear
homeomorphism `Plane ≃ ℂ`. Neither the polygonality nor the boundedness
hypothesis is needed.
-/
import LatticeProb.Topology.PolygonalJaniszewskiProved
import LatticeProb.Topology.Unicoherence

noncomputable section

open Set

namespace LatticeProb

open Janiszewski

/-- **Unicoherence of the plane.** The frontier of a component of the complement
of a closed connected plane set is preconnected. -/
theorem isPreconnected_frontier_connectedComponentIn_compl {A : Set Plane} (hA : IsClosed A)
    (hAc : IsConnected A) {p : Plane} (hp : p ∉ A) :
    IsPreconnected (frontier (connectedComponentIn Aᶜ p)) := by
  set e := planeEquiv.toHomeomorph
  have hK : IsClosed (e '' A) := e.isClosedMap A hA
  have hKc : IsConnected (e '' A) := hAc.image e e.continuous.continuousOn
  have himage : e '' connectedComponentIn Aᶜ p = connectedComponentIn (e '' A)ᶜ (e p) := by
    rw [e.image_connectedComponentIn (s := Aᶜ) (x := p) hp, image_compl_eq e.bijective]
  have hep : e p ∈ (e '' A)ᶜ := by
    rw [← image_compl_eq e.bijective]
    exact mem_image_of_mem e hp
  have hmem : e '' connectedComponentIn Aᶜ p ∈ Topology.connectedComponentsIn (e '' A)ᶜ :=
    himage ▸ mem_image_of_mem _ hep
  have hfr := Topology.isConnected_frontier_of_mem_connectedComponentsIn_compl hK hKc hmem
  rw [← e.image_frontier] at hfr
  have h := hfr.isPreconnected.image e.symm e.symm.continuous.continuousOn
  simpa only [image_image, Homeomorph.symm_apply_apply, image_id'] using h

/-- The frozen polygonal form of unicoherence holds; the polygonality and boundedness
hypotheses are not needed. -/
theorem polygonalUnicoherence : PolygonalUnicoherence := by
  rintro A - hA hAc F ⟨p, hp, rfl⟩ -
  exact isPreconnected_frontier_connectedComponentIn_compl hA.isClosed hAc hp

end LatticeProb
