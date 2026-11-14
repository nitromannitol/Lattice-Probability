/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftLower at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_shifted_sq_rate {D T : ℝ} (hD : 1 ≤ D)
    (hT : max (3 * D) (D^2) < T) :
    3 < T / D ∧
      (Real.log T)^2 / 4 ≤ (Real.log (T / D))^2 := by
  have hD0 : 0 < D := by linarith
  have hTD : 3 < T / D := by
    apply (lt_div_iff₀ hD0).2
    exact (le_max_left _ _).trans_lt hT
  have hT0 : 0 < T := by
    have hh : 3 * D < T := (le_max_left _ _).trans_lt hT
    nlinarith
  have hD2 : D^2 ≤ T := (le_max_right _ _).trans hT.le
  have hlogD : 2 * Real.log D ≤ Real.log T := by
    have hh := Real.log_le_log (by positivity : 0 < D^2) hD2
    rw [Real.log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hhalf : Real.log T / 2 ≤ Real.log (T / D) := by
    rw [Real.log_div hT0.ne' hD0.ne']
    linarith
  have hlogT : 0 ≤ Real.log T := (Real.log_pos (by
    have hh : 3 * D < T := (le_max_left _ _).trans_lt hT
    nlinarith : 1 < T)).le
  have hlogTD : 0 ≤ Real.log (T / D) :=
    (Real.log_pos (by linarith : 1 < T / D)).le
  refine ⟨hTD, ?_⟩
  nlinarith [sq_nonneg (Real.log (T / D) - Real.log T / 2)]

end SupercriticalLQGUniqueness.B2.DG20Conc
