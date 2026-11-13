/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyImage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.CanonicalCuts




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Convex ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

def mappedSingleton (a : ℚ) (p : ℚ × ℚ) : Exponent.PolygonalCost.RatPolygon where
  edges := 0
  vertices _ := mappedRatPoint a p

def canonicalImagePolygonFamily (a : ℚ) (P : Exponent.PolygonalCost.RatPolygon) :
    Exponent.PolygonalCost.RatPolygonFamily where
  last := P.edges
  paths i := if h : i.val < P.edges then
      canonicalMappedSegmentPolygon a
        (P.vertices ⟨i.val, Nat.lt_succ_of_lt h⟩)
        (P.vertices ⟨i.val+1, by omega⟩)
    else mappedSingleton a (P.vertices (Fin.last P.edges))

theorem ratPolygon_vertex_fin (P : Exponent.PolygonalCost.RatPolygon) (i : Fin (P.edges+1)) :
    P.vertex i.val = ratComplex (P.vertices i) := by
  have hidx : (⟨min i.val P.edges, Nat.lt_succ_of_le (min_le_right _ _)⟩ :
      Fin (P.edges+1)) = i := Fin.ext (Nat.min_eq_left (by omega))
  simp [Exponent.PolygonalCost.RatPolygon.vertex, ratComplex, hidx]

theorem canonicalImagePolygonFamily_edge (a : ℚ) (P : Exponent.PolygonalCost.RatPolygon)
    (i : Fin P.edges) :
    (canonicalImagePolygonFamily a P).paths i.castSucc =
      canonicalMappedSegmentPolygon a
        (P.vertices i.castSucc)
        (P.vertices i.succ) := by
  simp [canonicalImagePolygonFamily, i.isLt]
  congr 1

theorem canonicalImagePolygonFamily_last (a : ℚ) (P : Exponent.PolygonalCost.RatPolygon) :
    (canonicalImagePolygonFamily a P).paths (Fin.last P.edges) =
      mappedSingleton a (P.vertices (Fin.last P.edges)) := by
  simp [canonicalImagePolygonFamily]


end SupercriticalLQGUniqueness.Exponent.InwardMap
