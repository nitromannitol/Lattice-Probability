/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.QPosClosure at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P8FullPath
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P9FullPathClosure
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5Closure

 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem dg20ExponentPositive_proved : Iface.DG20ExponentPositive :=
  dg20ExponentPositive_of_fullPathComparison P8.dgffWhiteNoiseFullPathComparison_proved

end SupercriticalLQGUniqueness.B2.QPos
