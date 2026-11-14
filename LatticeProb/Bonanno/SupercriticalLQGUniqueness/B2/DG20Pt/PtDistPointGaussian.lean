/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalPointTail
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Straight

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_phi_point_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (k : ℕ) (hk : 0 < k) (z : ℂ) (y : ℝ) (hy : 0 ≤ y) :
    P {ω | y ≤ |phiMN W P 0 k z ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-y ^ 2 / (2 * ((k : ℝ) * Real.log 2)))) := by
  obtain ⟨v, hv, hlaw⟩ := hasLaw_phiMN hW k z
  have hv0 : 0 < (v : ℝ) := by
    rw [hv]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (by norm_num))
  have ht := tail_abs_of_hasLaw (P := P) hv0 hlaw hy
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact (ENNReal.ofReal_le_ofReal (by simpa only [hv] using ht))

end SupercriticalLQGUniqueness.B2.DG20Pt
