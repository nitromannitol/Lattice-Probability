/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.CellGradientCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.FieldBound




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem segCost_inwardMap_on_cell_gradient_le (a ξ G : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 1/256) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    (z w : ℂ) (hre : SameAxisCell z.re w.re)
    (him : SameAxisCell z.im w.im)
    (hpath : ∀ u ∈ Icc (0:ℝ) 1,
      segPath z w u ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    segCost ξ f (inwardMap a z) (inwardMap a w) ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp (32*Real.sqrt 2*ξ*(a*G))) *
        segCost ξ f z w := by
  have h := segCost_inwardMap_on_cell_le a ξ (32*Real.sqrt 2*a*G)
    ha0 ha hξ f z w hre him (fun u hu =>
      inwardMap_field_difference_le a G ha0 ha hG0 f hfd hG (hpath u hu))
  convert h using 1
  ring


end SupercriticalLQGUniqueness.Exponent.InwardMap
