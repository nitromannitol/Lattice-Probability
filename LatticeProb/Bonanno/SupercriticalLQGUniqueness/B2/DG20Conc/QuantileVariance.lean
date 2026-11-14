/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.QuantileVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 

theorem truncated_quantile_ratio_le (hW : IsWhiteNoise P W) (Q : PsiParams)
    (ξ : ℝ) {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (n : ℕ) :
    ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) /
      ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
      exp (sqrt (2 * Var[L24.logLenPsi ξ Q W P n; P]) / p) := by
  have := hW.isProbabilityMeasure
  obtain ⟨_, _, hLp⟩ := L24.psi_memLp_variance hW Q ξ
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  exact L24.ratio_le_of_variance hψ.cont hψ.meas (hLp n).1 hp0 hp

end SupercriticalLQGUniqueness.B2.DG20Conc
