/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAroundLen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePUpperUnion
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenHeat
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.MetricGeometry LQGMetric.DFGPS

theorem j1_lfpp_len_image_affine (ξ : ℝ) (g : ℂ → ℝ)
    (hg : Continuous g) {r : ℝ} (hr : 0 < r) (c : ℂ)
    (P : ℝ → ℂ) (a b : ℝ) :
    (lfppContMetric ξ g hg).len (fun t => c + (r : ℂ) * P t) a b =
      ENNReal.ofReal r *
        (lfppContMetric ξ (fun z => g (c + (r : ℂ) * z))
          (hg.comp (by fun_prop : Continuous
            (fun z : ℂ => c + (r : ℂ) * z)))).len P a b := by
  let hg' : Continuous (fun z => g (c + (r : ℂ) * z)) :=
    hg.comp (by fun_prop)
  have hpoint (x y : ℂ) :
      edist ((lfppContMetric ξ g hg).pt (c + (r : ℂ) * x))
        ((lfppContMetric ξ g hg).pt (c + (r : ℂ) * y)) =
      ENNReal.ofReal r *
        edist ((lfppContMetric ξ (fun z => g (c + (r : ℂ) * z)) hg').pt x)
          ((lfppContMetric ξ (fun z => g (c + (r : ℂ) * z)) hg').pt y) := by
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal ((lfppD ξ g (c + (r : ℂ) * x)
      (c + (r : ℂ) * y)).toReal) =
      ENNReal.ofReal r *
        ENNReal.ofReal ((lfppD ξ (fun z => g (c + (r : ℂ) * z)) x y).toReal)
    rw [ENNReal.ofReal_toReal (lfppD_ne_top hg _ _),
      ENNReal.ofReal_toReal (lfppD_ne_top hg' _ _)]
    have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    simpa [lfppD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using
      (lfppDOn_affine ξ g (S := Set.univ) (S' := Set.univ)
        (b := c) (c := (r : ℂ)) hc (by simp) x y)
  unfold ContMetric.len
  change curveLength ((lfppContMetric ξ g hg).pt ∘
      (fun t => c + (r : ℂ) * P t)) a b = _
  exact eVariationOn_eq_mul_of_edist
    (fun s t => hpoint (P s) (P t)) (Set.Icc a b)

end SupercriticalLQGUniqueness.B2.DG20Conc
