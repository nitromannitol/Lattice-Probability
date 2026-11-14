/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianUniform
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_lfppDOn_image_mul
    (ξ : ℝ) (g : ℂ → ℝ) (U : Set ℂ) (z w : ℂ)
    (r : ℝ) (hr : 0 < r) :
    lfppDOn ξ g ((fun x : ℂ => (r : ℂ) * x) '' U)
      ((r : ℂ) * z) ((r : ℂ) * w) =
      ENNReal.ofReal r *
        lfppDOn ξ (fun x => g ((r : ℂ) * x)) U z w := by
  simpa only [image_singleton, crossLenIn_singleton] using
    (crossLenIn_image_mul ξ g U {z} {w} hr)

end SupercriticalLQGUniqueness.B2.DG20Pt
