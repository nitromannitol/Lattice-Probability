/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.MappedSegment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.RationalCuts




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric.LFPP

 
def ratComplex (p : ℚ × ℚ) : ℂ :=
  ((p.1:ℝ):ℂ) + ((p.2:ℝ):ℂ)*Complex.I

 
def ratLinePoint (p q : ℚ × ℚ) (t : ℚ) : ℚ × ℚ :=
  (p.1+t*(q.1-p.1), p.2+t*(q.2-p.2))

 
def mappedRatPoint (a : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  (1/2+latticeCoordRat a (p.1-1/2),
    1/2+latticeCoordRat a (p.2-1/2))

theorem ratComplex_line (p q : ℚ × ℚ) (t : ℚ) :
    ratComplex (ratLinePoint p q t) =
      segPath (ratComplex p) (ratComplex q) (t:ℝ) := by
  apply Complex.ext <;>
    simp [ratComplex, ratLinePoint, segPath, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]

theorem mappedRatPoint_complex (a : ℚ) (ha : 0 ≤ a) (p : ℚ × ℚ) :
    ratComplex (mappedRatPoint a p) = inwardMap (a:ℝ) (ratComplex p) := by
  apply Complex.ext
  · simpa [ratComplex, mappedRatPoint, inwardMap_re] using
      (inwardAxis_rational a p.1 ha).symm
  · simpa [ratComplex, mappedRatPoint, inwardMap_im] using
      (inwardAxis_rational a p.2 ha).symm

 

def mappedSegmentPolygon (a : ℚ) (p q : ℚ × ℚ)
    (n : ℕ) (t : Fin (n+1) → ℚ) : Exponent.PolygonalCost.RatPolygon where
  edges := n
  vertices i := mappedRatPoint a (ratLinePoint p q (t i))

 
def cutTime (n : ℕ) (t : Fin (n+1) → ℚ) (j : ℕ) : ℚ :=
  t ⟨min j n, Nat.lt_succ_of_le (min_le_right j n)⟩

theorem cutTime_zero (n : ℕ) (t : Fin (n+1) → ℚ) :
    cutTime n t 0 = t 0 := rfl

theorem cutTime_last (n : ℕ) (t : Fin (n+1) → ℚ) :
    cutTime n t n = t (Fin.last n) := by
  simp only [cutTime, min_self]
  rfl

theorem cutTime_mono (n : ℕ) (t : Fin (n+1) → ℚ)
    (hm : StrictMono t) (j : ℕ) :
    cutTime n t j ≤ cutTime n t (j+1) := by
  unfold cutTime
  apply hm.monotone
  exact Fin.mk_le_mk.mpr (by omega)

theorem mappedSegmentPolygon_vertex (a : ℚ) (p q : ℚ × ℚ)
    (n : ℕ) (t : Fin (n+1) → ℚ) (j : ℕ) :
    (mappedSegmentPolygon a p q n t).vertex j =
      ratComplex (mappedRatPoint a (ratLinePoint p q (cutTime n t j))) := rfl


end SupercriticalLQGUniqueness.Exponent.InwardMap
