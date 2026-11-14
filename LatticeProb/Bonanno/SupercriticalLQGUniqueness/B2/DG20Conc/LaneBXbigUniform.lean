/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigUniform at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigLaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB_Xbig_gaussian_tail_uniform (Q : PsiParams) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ x : ℝ, 0 < x →
      P {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
          (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} ≤
        ENNReal.ofReal (C * Real.exp (-(c * x ^ 2))) := by
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  obtain ⟨C, c, hC, hc, ht⟩ :=
    laneB_Xbig_gaussian_tail LQGDimension.ExistAsm.stdP W₀ hW₀ Q
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P W hW x hx
  rw [laneB_Xbig_tail_eq P LQGDimension.ExistAsm.stdP W W₀ hW hW₀ Q x]
  exact ht x hx

end SupercriticalLQGUniqueness.B2.DG20Conc
