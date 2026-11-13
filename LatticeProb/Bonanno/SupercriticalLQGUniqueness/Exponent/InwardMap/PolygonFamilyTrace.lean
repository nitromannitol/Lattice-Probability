/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyTrace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonTraceLast




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Convex

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric.LFPP

theorem mappedSingleton_trace (a : ℚ) (ha : 0 ≤ a) (p : ℚ × ℚ) :
    (mappedSingleton a p).path '' Icc (0:ℝ) 1 =
      {inwardMap (a:ℝ) (ratComplex p)} := by
  rw [show (mappedSingleton a p).path =
      Exponent.PolygonCofinality.polygonPath (mappedSingleton a p).vertex 0 from rfl,
    Exponent.PaidDuality.polygonPath_trace]
  simpa [mappedSingleton, Exponent.PolygonalCost.RatPolygon.vertex, ratComplex] using
    congrArg (fun z : ℂ => ({z} : Set ℂ)) (mappedRatPoint_complex a ha p)

theorem canonicalImagePolygonFamily_trace (a : ℚ) (ha : 0 ≤ a)
    (P : Exponent.PolygonalCost.RatPolygon) :
    (canonicalImagePolygonFamily a P).trace =
      inwardMap (a:ℝ) '' (P.path '' Icc (0:ℝ) 1) := by
  let F := canonicalImagePolygonFamily a P
  have htrace : F.trace = ⋃ i : Fin (P.edges+1),
      (F.paths i).path '' Icc (0:ℝ) 1 := by
    ext z
    simp only [Exponent.PolygonalCost.RatPolygonFamily.trace, Exponent.PaidDuality.polygonPathsTrace,
      Finset.mem_univ, Set.iUnion_true]
    rfl
  rw [htrace]
  change (⋃ i : Fin (P.edges+1), (F.paths i).path '' Icc (0:ℝ) 1) =
    inwardMap (a:ℝ) ''
      (Exponent.PolygonCofinality.polygonPath P.vertex P.edges '' Icc (0:ℝ) 1)
  rw [polygonPath_trace_edges_last]
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [canonicalImagePolygonFamily_edge] at hi
      rw [canonicalMappedSegment_trace a ha] at hi
      obtain ⟨w, hw, rfl⟩ := hi
      refine ⟨w, Or.inr ?_, rfl⟩
      rw [Exponent.PaidDuality.segPath_trace] at hw
      have h0 := ratPolygon_vertex_fin P j.castSucc
      have h1 := ratPolygon_vertex_fin P j.succ
      rw [← h0, ← h1] at hw
      exact Set.mem_iUnion_of_mem j.val
        (Set.mem_iUnion_of_mem (Finset.mem_range.mpr j.isLt) hw)
    · rw [canonicalImagePolygonFamily_last, mappedSingleton_trace a ha] at hi
      have hz : z = inwardMap (a:ℝ) (ratComplex (P.vertices (Fin.last P.edges))) := by
        simpa using hi
      rw [hz]
      refine ⟨P.vertex P.edges, Or.inl (by simp), ?_⟩
      congr 1
      simpa only [Fin.val_last] using
        (ratPolygon_vertex_fin P (Fin.last P.edges))
  · rintro ⟨w, hw, rfl⟩
    rcases hw with hlast | hedge
    · have hw : w = P.vertex P.edges := by simpa using hlast
      rw [hw]
      have hend := ratPolygon_vertex_fin P (Fin.last P.edges)
      simp only [Fin.val_last] at hend
      rw [hend]
      refine Set.mem_iUnion_of_mem (Fin.last P.edges) ?_
      rw [canonicalImagePolygonFamily_last, mappedSingleton_trace a ha]
      simp
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hedge
      obtain ⟨hjn, hseg⟩ := Set.mem_iUnion.mp hj
      let i : Fin P.edges := ⟨j, Finset.mem_range.mp hjn⟩
      refine Set.mem_iUnion_of_mem i.castSucc ?_
      rw [canonicalImagePolygonFamily_edge]
      rw [canonicalMappedSegment_trace a ha, Exponent.PaidDuality.segPath_trace]
      refine ⟨w, ?_, rfl⟩
      have h0 := ratPolygon_vertex_fin P i.castSucc
      have h1 := ratPolygon_vertex_fin P i.succ
      change w ∈ [P.vertex j -[ℝ] P.vertex (j+1)] at hseg
      have hi0 : i.castSucc.val = j := rfl
      have hi1 : i.succ.val = j+1 := rfl
      rw [hi0] at h0
      rw [hi1] at h1
      simpa only [← h0, ← h1] using hseg


end SupercriticalLQGUniqueness.Exponent.InwardMap
