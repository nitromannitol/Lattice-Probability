/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonalCost.PaidLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.PolygonFull




 



set_option autoImplicit false

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.PolygonalCost

open LQGMetric

 
theorem rectLen_le_polygon_family {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (hadmitted : LQGMetric.Disconnects
      (Exponent.PaidDuality.polygonPathsTrace s v n) Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ)
    (k : Fin 4) (ξ : ℝ) (f : ℂ → ℝ) :
    DDDF.rectLen ξ f (Exponent.PaidDuality.centralRect k) ≤
      ∑ i ∈ s, lfppLen ξ f (Exponent.PolygonCofinality.polygonPath (v i) (n i)) := by
  obtain ⟨P, hP, hcost⟩ :=
    Exponent.PaidDuality.paid_central_rect_of_polygon_paths s v n hadmitted k ξ f
  exact (DDDF.crossLenIn_le_lfppLen hP).trans hcost


end SupercriticalLQGUniqueness.Exponent.PolygonalCost
