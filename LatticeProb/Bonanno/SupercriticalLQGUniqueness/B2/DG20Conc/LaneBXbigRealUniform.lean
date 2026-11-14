/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigRealUniform at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigUniform

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 



theorem laneB_Xbig_real_gaussian_tail_uniform (Q : PsiParams) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ x : ℝ, 0 < x →
      P {ω | x ≤ T20C.Xbig Q W P ω} ≤
        ENNReal.ofReal (C * Real.exp (-(c * x ^ 2))) := by
  obtain ⟨C, c, hC, hc, ht⟩ := laneB_Xbig_gaussian_tail_uniform Q
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P W hW x hx
  have hsub : {ω | x ≤ T20C.Xbig Q W P ω} ⊆
      {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
          (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} := by
    intro ω hω
    exact ENNReal.ofReal_le_of_le_toReal hω
  exact (measure_mono hsub).trans (ht P W hW x hx)

end SupercriticalLQGUniqueness.B2.DG20Conc
