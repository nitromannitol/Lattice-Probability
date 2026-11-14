/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateCompact at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateMerge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.TailRateCompact

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_rate_compact_patch (H c : ℝ)
    (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 < T → T ≤ Real.exp H →
      1 ≤ C * Real.exp
        (-c * (Real.log T) ^ 2 / Real.log (Real.log T)) := by
  let H' : ℝ := max H 9
  have hH' : 9 ≤ H' := le_max_right _ _
  have hM : 9 ≤ Real.exp H' := by
    have he := Real.add_one_le_exp H'
    linarith
  let C : ℝ := 2 * Real.exp
    (c * (Real.log (Real.exp H')) ^ 2 *
      (1 + (Real.log (Real.log 3))⁻¹))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T hT hTH
  have hT' : T ≤ Real.exp H' :=
    hTH.trans (Real.exp_le_exp.mpr (le_max_left _ _))
  have hh := tail_rate_compact_bound 1 c (Real.exp H') T
    (by norm_num) hc hM hT hT'
  simpa only [C, one_add_one_eq_two] using hh.2.2.2

end SupercriticalLQGUniqueness.B2.DG20Pt
