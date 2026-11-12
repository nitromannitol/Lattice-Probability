/-
# Simple polygonal access rays and Torhorst's theorem

For a compact locally connected set `K ⊆ ℂ`, every frontier point `a` of a complementary component `C` of `K`
is the limit of a simple polygonal ray with all edges in `C`: consecutive vertices distinct, consecutive edges
meeting only at their common vertex, and edges two or more steps apart disjoint. The ray is obtained from the
access chains of `exists_access_chains`, cut down to simple pieces by `exists_simple_pieces_of_chains` and
flattened by `exists_simple_ray_of_simple_pieces`.

Together with `torhorstSimpleLoop_of_access_rays` this proves Torhorst's theorem: the frontier of every
complementary component of a nondegenerate locally connected plane continuum without cut points is a simple
closed curve.
-/
import LatticeProb.Topology.BoundaryAccessChains
import LatticeProb.Topology.PolygonalPieces
import LatticeProb.Topology.PolygonalRayFlatten
import LatticeProb.Topology.TorhorstFromAccess

open Set Filter Topology Metric

namespace LatticeProb.Topology

/-- **Simple polygonal access rays.** Let `K ⊆ ℂ` be compact and locally connected, `C` a connected
component of `Kᶜ` and `a ∈ frontier C`. Then `a` is the limit of a simple polygonal ray with all edges in
`C`: a vertex sequence `v` with consecutive vertices distinct, consecutive edges meeting only at their common
vertex and edges two or more steps apart disjoint. -/
theorem exists_simple_access_ray {K : Set ℂ} (hK : IsCompact K) (hlc : IsLocallyConnectedSet K)
    {C : Set ℂ} (hC : C ∈ connectedComponentsIn Kᶜ) {a : ℂ} (ha : a ∈ frontier C) :
    ∃ v : ℕ → ℂ, (∀ n, v n ≠ v (n + 1)) ∧
      (∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)}) ∧
      (∀ n m, n + 2 ≤ m →
        Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1)))) ∧
      Tendsto v atTop (𝓝 a) ∧ ∀ n, segment ℝ (v n) (v (n + 1)) ⊆ C := by
  obtain ⟨σ, hσ, hjoin, hfar, h0, hσC, hσa⟩ := exists_access_chains hK hlc hC ha
  obtain ⟨L, hL, -, hlen, hLjoin, hLnext, hLfar, hLσ⟩ :=
    exists_simple_pieces_of_chains σ hσ hjoin hfar h0
  obtain ⟨v, hne, hadj, hvfar, hvC, hvlate⟩ :=
    exists_simple_ray_of_simple_pieces L hL hlen hLjoin hLnext hLfar
  refine ⟨v, hne, hadj, hvfar, ?_,
    fun n => (hvC n).trans (iUnion_subset fun j => (hLσ j).trans (hσC j))⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hσa ε hε
  obtain ⟨k, hk⟩ := hvlate N
  refine ⟨k, fun m hm => ?_⟩
  obtain ⟨j, hNj, hj⟩ := hk m hm
  exact hN j hNj (hLσ j hj)

/-- **Torhorst's theorem.** The frontier of every complementary component of a nondegenerate locally
connected continuum `K ⊆ ℂ` without cut points is a simple closed curve. -/
theorem torhorstSimpleLoop : TorhorstSimpleLoop :=
  torhorstSimpleLoop_of_access_rays fun _K hK _ _ hKlc _ _C hC _a ha =>
    exists_simple_access_ray hK hKlc hC ha

end LatticeProb.Topology
