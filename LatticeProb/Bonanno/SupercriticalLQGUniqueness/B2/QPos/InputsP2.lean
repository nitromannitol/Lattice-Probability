/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.InputsP2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2PathSum
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput

 














set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
def Excursion.Visits {V : Type*} (γ : Excursion V) (z : V) : Prop :=
  ∃ j, γ.2 j = z

 
def ExcursionEncircles (n : ℕ) (γ : Excursion (DGFFSite n)) : Prop :=
  ∃ p : List (DGFFSite n), IsDGFFAroundPath n p ∧ ∀ z ∈ p, γ.Visits z

namespace InputsP2

 


def CircuitMass : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ n : ℕ, 4 ≤ n →
    m ≤ ∑' γ : Excursion (DGFFSite n),
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ

end InputsP2

end SupercriticalLQGUniqueness.B2.QPos
