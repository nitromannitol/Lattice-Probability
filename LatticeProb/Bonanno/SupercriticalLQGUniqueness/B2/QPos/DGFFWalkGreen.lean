/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFWalkGreen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFGaussian

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def totalRate (i : V) : ℝ := G.boundary i + ∑ j, G.edge i j

 
def killedTransition : Matrix V V ℝ := fun i j => G.edge i j / G.totalRate i

theorem precision_eq_totalRate_sub_edge (i j : V) :
    G.precision i j = (if i = j then G.totalRate i else 0) - G.edge i j := by
  by_cases h : i = j
  · subst j
    simp [precision, totalRate, G.edge_self]
  · simp [precision, h]

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
