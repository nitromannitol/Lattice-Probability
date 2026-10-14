/-
# Separation at an isolated polygonal edge

Half-open crossing parity is constant on connected sets avoiding a closed
polygonal chain. At an isolated interior point of an edge it changes by one.
We combine these two proved facts to force intersection for every preconnected
set joining the two local sides, and choose the nonlevel ray direction from the
finite edge family. For cyclic vertex lists, closedness is derived by endpoint
cancellation. No separation or general-position assumption is required.
-/
import LatticeProb.Topology.PolygonalParity



open Metric Set
namespace LatticeProb.Topology.PolygonalParity

/-- A preconnected set containing two points of unequal crossing parity meets
 the edge trace. The direction must be nonlevel for each edge. -/
theorem inter_cover_nonempty_of_parity_ne {u : Plane} {L : List Piece}
    (hu : Plane.IsDirection u) (hL : ∀ P ∈ L, hgt u P.1 ≠ hgt u P.2)
    (hC : IsClosedChain L) {S : Set Plane} (hS : IsPreconnected S)
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) (hne : parity u L x ≠ parity u L y) :
    (S ∩ cover L).Nonempty := by
  by_contra hempty
  apply hne
  exact parity_eq_of_isPreconnected hu hL hC hS
    (fun z hz hzc => hempty ⟨z, hz, hzc⟩) hx hy

/-- **Local polygonal separation.** Around an isolated interior point of an
edge of a finite closed nondegenerate chain, a unit direction and a positive
radius exist such that every preconnected set joining the two opposite ray
points meets the chain. The direction is constructed from the finite edges. -/
theorem exists_local_separation {L₁ L₂ : List Piece} {a b p : Plane}
    (hnd : ∀ P ∈ L₁ ++ (a, b) :: L₂, P.Nondeg)
    (hC : IsClosedChain (L₁ ++ (a, b) :: L₂))
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ →
        p - t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
        p + t • u ∉ cover (L₁ ++ (a, b) :: L₂) ∧
        ∀ S : Set Plane, IsPreconnected S → p - t • u ∈ S → p + t • u ∈ S →
          (S ∩ cover (L₁ ++ (a, b) :: L₂)).Nonempty := by
  obtain ⟨u, hu, hL⟩ := exists_direction_hgt_ne (L₁ ++ (a, b) :: L₂) hnd
  obtain ⟨δ, hδ, hflip⟩ := parity_flip hu hL hp h1 h2
  refine ⟨u, hu, δ, hδ, fun t ht htδ => ?_⟩
  obtain ⟨hm, hplus, heq⟩ := hflip t ht htδ
  refine ⟨hm, hplus, fun S hS hx hy => ?_⟩
  apply inter_cover_nonempty_of_parity_ne hu hL hC hS hx hy
  intro hequal
  have hone : (1 : ZMod 2) = 0 := by
    have h := heq.symm.trans hequal
    exact add_left_cancel (h.trans (add_zero _).symm)
  exact one_ne_zero hone

/-- The local separation theorem for an actual cyclic vertex list. Its
closed-chain property is produced by the cyclic endpoint cancellation proof. -/
theorem exists_local_separation_edgesOf (vs : List Plane) {L₁ L₂ : List Piece}
    {a b p : Plane} (hedges : edgesOf vs = L₁ ++ (a, b) :: L₂)
    (hnd : ∀ P ∈ edgesOf vs, P.Nondeg)
    (hp : p ∈ openSegment ℝ a b) (h1 : p ∉ cover L₁) (h2 : p ∉ cover L₂) :
    ∃ u : Plane, Plane.IsDirection u ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ →
        p - t • u ∉ cover (edgesOf vs) ∧ p + t • u ∉ cover (edgesOf vs) ∧
        ∀ S : Set Plane, IsPreconnected S → p - t • u ∈ S → p + t • u ∈ S →
          (S ∩ cover (edgesOf vs)).Nonempty := by
  have hC := isClosedChain_edgesOf vs
  rw [hedges] at hC hnd ⊢
  exact exists_local_separation hnd hC hp h1 h2

end LatticeProb.Topology.PolygonalParity
