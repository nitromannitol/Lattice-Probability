/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsDGFF

 




set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.QPos

 
def IsDGFFAroundPath (n : ℕ) (p : List (DGFFSite n)) : Prop :=
  p.Nodup ∧ p.IsChain (fun z w => latticeAdjacent z.1 w.1) ∧
  (∀ z ∈ p, inDGFFAnnulus n z) ∧
  (∃ z w : DGFFSite n, p.head? = some z ∧ p.getLast? = some w ∧
    latticeAdjacent w.1 z.1) ∧
  ∀ q : List (DGFFSite n), IsDGFFAnnulusPath n q →
    ∃ z : DGFFSite n, z ∈ p ∧ z ∈ q

namespace Inputs

 


def DGFFCircuitLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 4 ≤ n → ∀ u : ℝ, 0 < u →
    ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) ≤
      boxDGFF n {h | ∃ p : List (DGFFSite n),
        IsDGFFAroundPath n p ∧
          ∀ z ∈ p, -u ≤ h z}

end Inputs
end SupercriticalLQGUniqueness.B2.QPos
