/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2Closure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2Main
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3CircuitMass

 




set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
theorem dgffCircuitLower_proved : Inputs.DGFFCircuitLower :=
  dgffCircuitLower_of_circuitMass circuitMass_proved

end SupercriticalLQGUniqueness.B2.QPos
