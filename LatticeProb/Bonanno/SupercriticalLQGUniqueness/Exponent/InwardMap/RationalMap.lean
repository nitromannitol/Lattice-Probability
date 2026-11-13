/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.RationalMap at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.Separation




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def latticeCoordRat (a t : ℚ) : ℚ :=
  max (min (max (min (t+32*a) ((1-64*a)*t-64*a)) ((1+64*a)*t))
      ((1-64*a)*t+64*a))
    (t-32*a)

theorem latticeCoordRat_cast (a t : ℚ) :
    ((latticeCoordRat a t : ℚ) : ℝ) = latticeCoord (a:ℝ) (t:ℝ) := by
  unfold latticeCoordRat latticeCoord
  norm_cast

theorem inwardAxis_rational (a t : ℚ) (ha : 0 ≤ a) :
    inwardAxis (a:ℝ) (t:ℝ) =
      ((1/2 + latticeCoordRat a (t-1/2) : ℚ) : ℝ) := by
  have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  rw [inwardAxis, ← latticeCoord_eq_inwardCoord (a:ℝ) ((t:ℝ)-1/2) haR]
  push_cast
  rw [latticeCoordRat_cast]
  congr 1
  push_cast
  ring

end SupercriticalLQGUniqueness.Exponent.InwardMap
