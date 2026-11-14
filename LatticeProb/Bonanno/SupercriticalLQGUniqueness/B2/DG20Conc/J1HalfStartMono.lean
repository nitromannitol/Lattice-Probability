/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfStartMono at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffHalfPower

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_half_start_of_full (Q : PsiParams) (K : ℕ) (T : ℝ)
    (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T) :
    (2 : ℝ)^((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T := by
  have hx : 0 ≤ (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) :=
    Real.rpow_nonneg (by positivity) _
  have hle : (1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) ≤
      (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) := by linarith
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle).trans_lt hT

end SupercriticalLQGUniqueness.B2.DG20Conc
