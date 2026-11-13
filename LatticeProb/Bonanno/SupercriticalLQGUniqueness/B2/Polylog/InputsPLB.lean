/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.InputsPLB at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.Polylog

 



def LFPPNormalizerExists : Prop :=
  ∀ ξ ε : Set.Ioi (0 : ℝ), ∃ a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a

 
theorem lfppNormalizerExists_of_existsUnique
    (h : ∀ ξ ε : Set.Ioi (0 : ℝ), ∃! a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a) :
    LFPPNormalizerExists :=
  fun ξ ε => (h ξ ε).exists

end SupercriticalLQGUniqueness.B2.Polylog
