/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Exponent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Gaussian
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA4_exponent_cancel (ξ Q : ℝ) :
    -(ξ * Q) + (ξ * min ξ Q - (min ξ Q) ^ 2 / 2) =
      -hitExponent ξ Q := by
  by_cases h : ξ ≤ Q
  · rw [min_eq_left h]
    simp only [hitExponent, if_pos h]
    ring
  · have h' : Q < ξ := lt_of_not_ge h
    rw [min_eq_right h'.le]
    simp only [hitExponent, if_neg h]
    ring

 

end SupercriticalLQGUniqueness.B2.DG20Conc
