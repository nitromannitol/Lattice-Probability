/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLambdaLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLambdaZero
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossSite

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_lambdaN_lower_of_inputs
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ,
          C⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (n : ℝ)) ≤
            lambdaN (ξ : ℝ) W P n := by
  obtain ⟨C, hC, hrel⟩ := hExp ξ Q hQ ζ hζ
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ W hW n
  have hbase : 1 ≤ lambdaN (ξ : ℝ) W P 0 :=
    pt_dist_lambdaN_zero_ge_one P W hW (ξ : ℝ)
  have hfac : 0 ≤ C⁻¹ * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (n : ℝ)) := by
    positivity
  have hscaled := le_mul_of_one_le_right hfac hbase
  have hnorm := (hrel P W hW n n le_rfl).1
  exact hscaled.trans (by simpa only [Nat.sub_self] using hnorm)

end SupercriticalLQGUniqueness.B2.DG20Pt
