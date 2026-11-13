/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PolygonalCost.Basic




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def inwardCoord (a t : ℝ) : ℝ :=
  if t ≤ -(3/2 : ℝ) then t + 32*a
  else if t ≤ -(1/2 : ℝ) then -(1/2 : ℝ) - 32*a + (1-64*a)*(t+1/2)
  else if t ≤ (1/2 : ℝ) then (1+64*a)*t
  else if t ≤ (3/2 : ℝ) then (1/2 : ℝ)+32*a+(1-64*a)*(t-1/2)
  else t-32*a

 
def inwardMap (a : ℝ) (z : ℂ) : ℂ :=
  Complex.mk (1/2 + inwardCoord a (z.re-1/2))
    (1/2 + inwardCoord a (z.im-1/2))

end SupercriticalLQGUniqueness.Exponent.InwardMap
