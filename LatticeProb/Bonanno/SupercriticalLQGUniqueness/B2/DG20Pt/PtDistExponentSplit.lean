/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistExponentSplit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTailDecay

 


set_option autoImplicit false
noncomputable section

open Set
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_positive_exponent_split
    (hPos : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q) :
    ∃ ζ β : ℝ, 0 < ζ ∧ 0 < β ∧
      0 < (ξ : ℝ) * Q - 3 * ζ - 2 * β := by
  have hξQ : 0 < (ξ : ℝ) * Q := mul_pos ξ.2 (hPos ξ Q hQ)
  refine ⟨(ξ : ℝ) * Q / 12, (ξ : ℝ) * Q / 8,
    by positivity, by positivity, ?_⟩
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Pt
