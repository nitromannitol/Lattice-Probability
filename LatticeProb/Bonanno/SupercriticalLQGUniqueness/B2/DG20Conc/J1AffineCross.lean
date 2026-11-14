/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BoundedRange
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem j1_crossLen_image_affine
    (ξ : ℝ) (g : ℂ → ℝ) (U E F : Set ℂ)
    {r : ℝ} (hr : 0 < r) (c : ℂ) :
    crossLenIn ξ g ((fun z => c + (r : ℂ) * z) '' U)
      ((fun z => c + (r : ℂ) * z) '' E)
      ((fun z => c + (r : ℂ) * z) '' F) =
    ENNReal.ofReal r *
      crossLenIn ξ (fun z => g (c + (r : ℂ) * z)) U E F := by
  have himg (S : Set ℂ) :
      (fun z => c + (r : ℂ) * z) '' S =
      (fun z => (1 : Circle) * z + c) ''
        ((fun z => (r : ℂ) * z) '' S) := by
    rw [Set.image_image]
    congr 1
    funext z
    simp [add_comm]
  rw [himg U, himg E, himg F,
    crossLenIn_image_motion ξ g _ _ _ (1 : Circle) c]
  simpa only [Circle.coe_one, one_mul, add_comm] using
    crossLenIn_image_mul ξ (fun z => g (z + c)) U E F hr

end SupercriticalLQGUniqueness.B2.DG20Conc
