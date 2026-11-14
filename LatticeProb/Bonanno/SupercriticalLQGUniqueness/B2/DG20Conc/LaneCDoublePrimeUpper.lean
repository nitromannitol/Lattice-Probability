/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDoublePrimeUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRectMotion

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP
open scoped ENNReal

theorem laneC_double_prime_long_mrect_imp {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {N b : ℝ} (hN : 12 ≤ N)
    (hlarge : ENNReal.ofReal (N * b) <
      (lfppContMetric ξ f hf).aroundDist laneCDoublePrimeAround
        laneCDoublePrimeInner laneCDoublePrimeOuter) :
    ∃ j : Fin 12, b < T20B.mrectLen ξ f 0
      (laneCTwelveMotionU j) (laneCTwelveMotionC j) 3 1 := by
  obtain ⟨j, hj⟩ := laneC_twelve_rect_long_imp hf hN hlarge
  exact ⟨j, by simpa only [laneC_twelve_rect_mrect] using hj⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
