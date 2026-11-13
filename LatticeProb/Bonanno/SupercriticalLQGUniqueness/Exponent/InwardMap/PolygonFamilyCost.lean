/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyCost at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyTrace




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Convex ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem source_polygon_edge_mem_closed (P : Exponent.PolygonalCost.RatPolygon)
    (hP : P.path '' Icc (0:ℝ) 1 ⊆ Exponent.PolygonalCost.closedSquareAnnulus)
    (i : Fin P.edges) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    segPath (ratComplex (P.vertices i.castSucc))
      (ratComplex (P.vertices i.succ)) u ∈ Exponent.PolygonalCost.closedSquareAnnulus := by
  have h0 := ratPolygon_vertex_fin P i.castSucc
  have h1 := ratPolygon_vertex_fin P i.succ
  have hmem : segPath (P.vertex i.val) (P.vertex (i.val+1)) u ∈
      P.path '' Icc (0:ℝ) 1 := by
    rw [Exponent.PolygonalCost.RatPolygon.path, Exponent.PaidDuality.polygonPath_trace]
    right
    refine Set.mem_iUnion_of_mem i.val ?_
    refine Set.mem_iUnion_of_mem (Finset.mem_range.mpr i.isLt) ?_
    rw [← Exponent.PaidDuality.segPath_trace]
    exact ⟨u, hu, rfl⟩
  rw [← h0, ← h1]
  exact hP hmem

theorem canonicalImagePolygonFamily_cost_le (a : ℚ) (ha0 : 0 ≤ a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (P : Exponent.PolygonalCost.RatPolygon)
    (hP : P.path '' Icc (0:ℝ) 1 ⊆ Exponent.PolygonalCost.closedSquareAnnulus) :
    (canonicalImagePolygonFamily a P).cost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) * lfppLen ξ f P.path := by
  let F := canonicalImagePolygonFamily a P
  let C := ENNReal.ofReal ((5/4:ℝ)*Real.exp
    (32*Real.sqrt 2*ξ*((a:ℝ)*G)))
  change (∑ i : Fin (P.edges+1), lfppLen ξ f (F.paths i).path) ≤
    C * lfppLen ξ f P.path
  rw [Fin.sum_univ_castSucc]
  have hlast : lfppLen ξ f (F.paths (Fin.last P.edges)).path = 0 := by
    rw [canonicalImagePolygonFamily_last]
    simp [mappedSingleton, Exponent.PolygonalCost.RatPolygon.path, Exponent.PolygonCofinality.polygonPath,
      DDDF.lfppLen_const]
  rw [hlast, add_zero]
  have hsum : (∑ i : Fin P.edges, lfppLen ξ f (F.paths i.castSucc).path) ≤
      ∑ i : Fin P.edges, C *
        segCost ξ f (P.vertex i.val) (P.vertex (i.val+1)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [canonicalImagePolygonFamily_edge]
    have hc := canonicalMappedSegment_cost_le a ha0 ha ξ G hξ hG0 f hfd hG
      (P.vertices i.castSucc) (P.vertices i.succ)
      (source_polygon_edge_mem_closed P hP i)
    have h0 := ratPolygon_vertex_fin P i.castSucc
    have h1 := ratPolygon_vertex_fin P i.succ
    have h1' : P.vertex (i.val+1) = ratComplex (P.vertices i.succ) := by
      simpa using h1
    rw [← h0, ← h1'] at hc
    exact hc
  calc
    (∑ i : Fin P.edges, lfppLen ξ f (F.paths i.castSucc).path) ≤
        ∑ i : Fin P.edges, C *
          segCost ξ f (P.vertex i.val) (P.vertex (i.val+1)) := hsum
    _ = C * lfppLen ξ f P.path := by
      rw [← Finset.mul_sum]
      have hsumrange :
          (∑ i : Fin P.edges, segCost ξ f (P.vertex i.val) (P.vertex (i.val+1))) =
          ∑ j ∈ Finset.range P.edges, segCost ξ f (P.vertex j) (P.vertex (j+1)) :=
        Fin.sum_univ_eq_sum_range
          (fun j => segCost ξ f (P.vertex j) (P.vertex (j+1))) P.edges
      rw [hsumrange]
      have hpoly := (Exponent.PolygonCofinality.polygonPath_data (ξ := ξ) (f := f)
        (S := (Set.univ : Set ℂ)) (convex_univ : Convex ℝ (Set.univ : Set ℂ))
        P.vertex P.edges (by simp)).2.2
      simpa [Exponent.PolygonalCost.RatPolygon.path] using congrArg (C * ·) hpoly.symm

end SupercriticalLQGUniqueness.Exponent.InwardMap
