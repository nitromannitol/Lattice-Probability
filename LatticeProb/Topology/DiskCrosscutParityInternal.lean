/-
# Closed ray-parity chains at original disk endpoints

Given actual simple finite disk crosscuts, construct the outside
completion at the original first and third circle points. Consecutive edge
boundaries cancel, their trace is the exact inside/outside union, every edge is
nondegenerate, and a nonlevel unit ray direction is produced. An actual second
disk path avoiding the first also avoids the completed loop; local parity
constancy forces equal parity at its original second and fourth endpoints.

This is an internal path-data theorem. The opposite parity of the two original
boundary intervals, needed for the disk alternation contradiction, is the circle endpoint jump proved in the endpoint modules.
-/
import LatticeProb.Topology.PolygonalParityChain
import LatticeProb.Topology.DiskOutsideArc
import LatticeProb.Topology.CircleAngleWindow



open Set
namespace LatticeProb.Topology.PolygonalParity

/-- **Original-endpoint closed parity chain (internal).** Actual finite simple
crosscut data produce a closed nonlevel ray-parity chain, and an avoiding second
path forces equal parity at the original second and fourth circle points.
The outside completion, edge closedness, ray genericity and avoidance are
constructed; none is an assumed separation result. -/
theorem exists_original_endpoint_parity_chain_internal (θ₁ θ₂ θ₃ θ₄ : ℝ)
    (h₁₂ : θ₁ < θ₂) (h₂₃ : θ₂ < θ₃) (h₃₄ : θ₃ < θ₄)
    (h₄₁ : θ₄ < θ₁ + 2 * Real.pi)
    (vs : List (ℝ × ℝ)) (hv : vs ≠ []) (hvs : IsSimplePolygonalChain vs)
    (hvhead : vs.head hv = (Real.cos θ₁, Real.sin θ₁))
    (hvlast : vs.getLast hv = (Real.cos θ₃, Real.sin θ₃))
    (hvD : polygonalChain vs ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (r : Path (Real.cos θ₂, Real.sin θ₂) (Real.cos θ₄, Real.sin θ₄))
    (hrD : range r ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hvr : Disjoint (polygonalChain vs) (range r)) :
    ∃ us : List (ℝ × ℝ), ∃ hu : us ≠ [], IsSimplePolygonalChain us ∧
      us.head hu = (Real.cos θ₁, Real.sin θ₁) ∧
      us.getLast hu = (Real.cos θ₃, Real.sin θ₃) ∧
      polygonalChain us \ {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ⊆
        {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
      ∃ u : Plane, Plane.IsDirection u ∧
        IsClosedChain (coordinateEdges (chainEdges vs ++ chainEdges us)) ∧
        (∀ P ∈ coordinateEdges (chainEdges vs ++ chainEdges us), hgt u P.1 ≠ hgt u P.2) ∧
        cover (coordinateEdges (chainEdges vs ++ chainEdges us)) =
          coordinateEquiv '' (polygonalChain vs ∪ polygonalChain us) ∧
        polygonalChain vs ∩ polygonalChain us =
          {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} ∧
        Disjoint (polygonalChain vs ∪ polygonalChain us) (range r) ∧
        parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos θ₂, Real.sin θ₂)) =
          parity u (coordinateEdges (chainEdges vs ++ chainEdges us))
            (coordinateEquiv (Real.cos θ₄, Real.sin θ₄)) := by
  have h13 := circle_point_ne_of_lt_lt_add_two_pi (h₁₂.trans h₂₃) (h₃₄.trans h₄₁)
  obtain ⟨us, hu, hus, huhead, hulast, q, _, hqrange, hqout, hqD⟩ :=
    exists_injective_polygonal_outside_completion θ₁ θ₃ h13
  have hvne : vs.head hv ≠ vs.getLast hv := by rw [hvhead, hvlast]; exact h13
  have hune : us.head hu ≠ us.getLast hu := by rw [huhead, hulast]; exact h13
  have htrace : coordinateEdgeTrace (chainEdges vs ++ chainEdges us) =
      polygonalChain vs ∪ polygonalChain us := by
    rw [coordinateEdgeTrace_append, coordinateEdgeTrace_chainEdges hv hvne,
      coordinateEdgeTrace_chainEdges hu hune]
  have hC := isClosedChain_coordinateEdges_append hv hu
    (hvhead.trans huhead.symm) (hvlast.trans hulast.symm)
  have hnd := nondeg_coordinateEdges_append hvs hus
  obtain ⟨u, huunit, hL⟩ := exists_direction_hgt_ne _ hnd
  have hcover : cover (coordinateEdges (chainEdges vs ++ chainEdges us)) =
      coordinateEquiv '' (polygonalChain vs ∪ polygonalChain us) := by
    rw [← coordinateEquiv_image_edgeTrace, htrace]
  have hends : ({(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} :
      Set (ℝ × ℝ)) ⊆ polygonalChain vs := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · rw [← hvhead]
      exact head_mem_polygonal_chain hv
    · rw [mem_singleton_iff] at hz
      rw [hz, ← hvlast]
      exact getLast_mem_polygonal_chain hv
  have hmeet : polygonalChain vs ∩ polygonalChain us =
      {(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} := by
    apply subset_antisymm
    · intro z hz
      rw [← hqD]
      exact ⟨hqrange.symm ▸ hz.2, hvD hz.1⟩
    · intro z hz
      exact ⟨hends hz, hqrange ▸ (inter_subset_left (hqD.symm ▸ hz))⟩
  have husr : Disjoint (polygonalChain us) (range r) := by
    apply disjoint_left.mpr
    intro z hzu hzr
    have hzends : z ∈ ({(Real.cos θ₁, Real.sin θ₁), (Real.cos θ₃, Real.sin θ₃)} :
        Set (ℝ × ℝ)) := by
      rw [← hqD]
      exact ⟨hqrange.symm ▸ hzu, hrD hzr⟩
    exact disjoint_left.mp hvr (hends hzends) hzr
  have hloopr : Disjoint (polygonalChain vs ∪ polygonalChain us) (range r) :=
    disjoint_union_left.mpr ⟨hvr, husr⟩
  have hrmiss : ∀ z ∈ coordinateEquiv '' range r,
      z ∉ cover (coordinateEdges (chainEdges vs ++ chainEdges us)) := by
    rintro z ⟨w, hwr, rfl⟩ hz
    rw [hcover] at hz
    obtain ⟨v, hvloop, heq⟩ := hz
    exact disjoint_left.mp hloopr (coordinateEquiv.injective heq ▸ hvloop) hwr
  have hrconn : IsPreconnected (coordinateEquiv '' range r) :=
    (isConnected_range r.continuous).isPreconnected.image coordinateEquiv
      continuous_coordinateEquiv.continuousOn
  have heq := parity_eq_of_isPreconnected huunit hL hC hrconn hrmiss
    (mem_image_of_mem coordinateEquiv r.source_mem_range)
    (mem_image_of_mem coordinateEquiv r.target_mem_range)
  exact ⟨us, hu, hus, huhead, hulast, hqrange ▸ hqout, u, huunit, hC, hL,
    hcover, hmeet, hloopr, heq⟩

end LatticeProb.Topology.PolygonalParity
