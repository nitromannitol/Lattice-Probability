/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PieceCost at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.AffineCells




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

 


theorem segCost_inwardMap_on_cell_le (a ξ δ : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 1/256) (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (z w : ℂ)
    (hre : SameAxisCell z.re w.re) (him : SameAxisCell z.im w.im)
    (hfield : ∀ u ∈ Icc (0:ℝ) 1,
      f (inwardMap a (segPath z w u)) ≤ f (segPath z w u)+δ) :
    segCost ξ f (inwardMap a z) (inwardMap a w) ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp (ξ*δ)) * segCost ξ f z w := by
  have hspeed : ‖inwardMap a w - inwardMap a z‖ ≤ (5/4:ℝ)*‖w-z‖ := by
    have h := (inwardMap_lipschitz a ha0 ha).dist_le_mul z w
    simpa only [dist_eq_norm, norm_sub_rev, NNReal.coe_div, NNReal.coe_ofNat] using h
  apply segCost_affine_image_le hξ f z w (inwardMap a z) (inwardMap a w) hspeed
  intro u hu
  rw [← inwardMap_affine_on_cells a z w hre him hu]
  exact hfield u hu


end SupercriticalLQGUniqueness.Exponent.InwardMap
