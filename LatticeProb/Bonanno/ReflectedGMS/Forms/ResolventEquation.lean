/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventEquation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.Resolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexTest
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea

/-!
# Coordinate equation for the full-form resolvent

Testing the checked full-domain weak resolvent identity against the existing
vertex indicator gives the ordinary-vertex generator equation.  Its origin in
the full form is essential: the pointwise equation alone neither determines a
unique solution on a transient network nor proves association with the
canonical reflected path law.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The weighted value of ReflectedWalk's vertex indicator is the corresponding
single-coordinate vector in `lp 2`. -/
theorem weightedValue_indic_eq_single
    [DecidableEq V] (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (v : V) :
    weightedValue m (G.indic v) (VertexTest.indic_hasSpeedL2 G m v) =
      lp.single 2 v (Real.sqrt (m v)) := by
  classical
  apply lp.ext
  funext w
  rw [weightedValue_apply, lp.single_apply]
  by_cases hw : w = v
  · subst w
    simp [ReflectedWalk.ConductanceGraph.indic]
  · simp [ReflectedWalk.ConductanceGraph.indic, hw]

private theorem mul_oneResolventFunction_eq_value_mul_sqrt
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (f : ValueSpace V) (v : V) :
    m v * oneResolventFunction G m f v =
      oneResolvent G m f v * Real.sqrt (m v) := by
  unfold oneResolventFunction unweight
  calc
    m v * (oneResolvent G m f v / Real.sqrt (m v)) =
        (Real.sqrt (m v) * Real.sqrt (m v)) *
          (oneResolvent G m f v / Real.sqrt (m v)) := by
      rw [Real.mul_self_sqrt (hm v).le]
    _ = oneResolvent G m f v * Real.sqrt (m v) := by
      field_simp [Real.sqrt_pos.2 (hm v)]

end ReflectedGMS.FullNetworkForm
