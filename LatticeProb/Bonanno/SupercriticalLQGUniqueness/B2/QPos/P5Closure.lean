/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5Closure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Final
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Closure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P9FullPathClosure

 











set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem dgffInductionLowerWindow_proved : Inputs.DGFFInductionLowerWindow :=
  P5.dgffInductionLowerWindow_of_circuitLower dgffCircuitLower_proved

 
theorem dg20ExponentPositive_of_fullPathComparison
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison) : Iface.DG20ExponentPositive :=
  dg20ExponentPositive_of_P5_fullPathComparison dgffInductionLowerWindow_proved hfull

end SupercriticalLQGUniqueness.B2.QPos
