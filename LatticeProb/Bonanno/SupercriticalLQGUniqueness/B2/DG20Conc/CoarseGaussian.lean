/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.CoarseGaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.ContinuousGaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep3

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 



theorem coarse_psi_variance_fixed_background (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) (K : ℕ)
    (V : ℂ → ℝ) (hV : Continuous V) :
    MemLp (fun ω => L23.logLen ξ (fun x => V x + psiMN Q W P 0 K x ω)) 2 P ∧
      Var[fun ω => L23.logLen ξ (fun x => V x + psiMN Q W P 0 K x ω); P] ≤
        ξ ^ 2 * (K * Real.log 2) := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  exact continuous_gaussian_log_cross_variance_le (by positivity)
    (T20B.isGaussianProcess_psiMN hW Q (Nat.zero_le K))
    hψ.cont hψ.meas (T20B.integral_psiMN hW Q (Nat.zero_le K))
    (fun x _ => T20B.variance_psiMN_le hW Q K x) V hV

end SupercriticalLQGUniqueness.B2.DG20Conc
