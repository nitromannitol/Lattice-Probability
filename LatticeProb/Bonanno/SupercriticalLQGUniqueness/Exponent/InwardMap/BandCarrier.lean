/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.BandCarrier at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.RationalCoords




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric.LFPP

def bandPolygon (n : ℕ) (v : ℕ → ℂ)
    (hv : ∀ i ≤ n, v i ∈ gaussRat) : Exponent.PolygonalCost.RatPolygon where
  edges := n
  vertices i := gaussRatCoords (v i.val) (hv i.val (Nat.le_of_lt_succ i.isLt))

theorem bandPolygon_vertex (n : ℕ) (v : ℕ → ℂ)
    (hv : ∀ i ≤ n, v i ∈ gaussRat) (j : ℕ) (hj : j ≤ n) :
    (bandPolygon n v hv).vertex j = v j := by
  simp only [bandPolygon, Exponent.PolygonalCost.RatPolygon.vertex, Nat.min_eq_left hj]
  change ratComplex (gaussRatCoords (v j) (hv j hj)) = v j
  exact ratComplex_gaussRatCoords (v j) (hv j hj)

theorem polygonPath_congr_of_le (v w : ℕ → ℂ) (n : ℕ)
    (h : ∀ i ≤ n, v i = w i) :
    Exponent.PolygonCofinality.polygonPath v n = Exponent.PolygonCofinality.polygonPath w n := by
  induction n with
  | zero => simp [Exponent.PolygonCofinality.polygonPath, h 0 le_rfl]
  | succ n ih =>
    rw [Exponent.PolygonCofinality.polygonPath, Exponent.PolygonCofinality.polygonPath]
    rw [ih (fun i hi => h i (hi.trans (Nat.le_succ n))),
      h n (Nat.le_succ n), h (n+1) le_rfl]

theorem bandPolygon_path (n : ℕ) (v : ℕ → ℂ)
    (hv : ∀ i ≤ n, v i ∈ gaussRat) :
    (bandPolygon n v hv).path = Exponent.PolygonCofinality.polygonPath v n := by
  exact polygonPath_congr_of_le _ _ n (bandPolygon_vertex n v hv)


end SupercriticalLQGUniqueness.Exponent.InwardMap
