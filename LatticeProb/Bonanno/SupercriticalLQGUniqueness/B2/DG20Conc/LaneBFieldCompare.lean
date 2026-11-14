/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFieldCompare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB_crossLen_compare_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U A B : Set ℂ)
    (hU : U ⊆ T20D.bigBox)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    crossLenIn ξ (fun x => phiMN W P 0 m x ω) U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
          crossLenIn ξ (fun x => psiMN Q W P 0 m x ω) U A B ∧
    crossLenIn ξ (fun x => psiMN Q W P 0 m x ω) U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) *
          crossLenIn ξ (fun x => phiMN W P 0 m x ω) U A B := by
  constructor
  · apply crossLenIn_le_of_abs_sub_le
    intro x hx
    exact T20D.abs_sub_le_Xbig Q hfin m (hU hx)
  · apply crossLenIn_le_of_abs_sub_le
    intro x hx
    rw [abs_sub_comm]
    exact T20D.abs_sub_le_Xbig Q hfin m (hU hx)

 



end SupercriticalLQGUniqueness.B2.DG20Conc
