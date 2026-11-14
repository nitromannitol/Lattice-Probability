/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CoarseRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2RawTails

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_coarse_rate_eq {ξ A M S T : ℝ}
    (hξ : 0 < ξ) (hA : 0 < A)
    (he : Real.exp (|ξ| * M) = S)
    (hlog : Real.log S = Real.log T / 2) :
    (M / A)^2 * 3 / Real.log 4 =
      (3 / (4 * ξ^2 * A^2 * Real.log 4)) * (Real.log T)^2 := by
  have hξM : ξ * M = Real.log T / 2 := by
    rw [← he, Real.log_exp] at hlog
    simpa only [abs_of_pos hξ] using hlog
  have hξ0 : ξ ≠ 0 := ne_of_gt hξ
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hlog40 : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hξ0, hA0, hlog40]
  nlinarith [congrArg (fun x : ℝ => x ^ 2) hξM]

end SupercriticalLQGUniqueness.B2.DG20Conc
