/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFDistance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFModel
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointCost

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
def latticeRadius (z : ℤ × ℤ) : ℕ := max z.1.natAbs z.2.natAbs

 
def dgffInnerRadius (n : ℕ) : ℕ := 2 ^ (n - 1)

 

def dgffOuterRadius (n : ℕ) : ℕ :=
  Nat.floor ((2 : ℝ) ^ ((n : ℝ) - 1 / 2))

 
def inDGFFAnnulus (n : ℕ) (z : DGFFSite n) : Prop :=
  dgffInnerRadius n < latticeRadius z.1 ∧
    latticeRadius z.1 ≤ dgffOuterRadius n

 
def IsDGFFAnnulusPath (n : ℕ) (p : List (DGFFSite n)) : Prop :=
  p.IsChain (fun z w => latticeAdjacent z.1 w.1) ∧
    (∀ z ∈ p, inDGFFAnnulus n z) ∧
    ∃ z w : DGFFSite n,
      p.head? = some z ∧ p.getLast? = some w ∧
      latticeRadius z.1 = dgffInnerRadius n + 1 ∧
      latticeRadius w.1 = dgffOuterRadius n

 
def dgffPathCost (n : ℕ) (ξ : ℝ) (h : EuclideanSpace ℝ (DGFFSite n))
    (p : List (DGFFSite n)) : ℝ :=
  inclusivePathCost (fun z => Real.exp (ξ * h z)) p

 

def dgffAnnulusDistance (n : ℕ) (ξ : ℝ)
    (h : EuclideanSpace ℝ (DGFFSite n)) : ℝ :=
  ⨅ p : {p : List (DGFFSite n) // IsDGFFAnnulusPath n p},
    dgffPathCost n ξ h p.1

end SupercriticalLQGUniqueness.B2.QPos
