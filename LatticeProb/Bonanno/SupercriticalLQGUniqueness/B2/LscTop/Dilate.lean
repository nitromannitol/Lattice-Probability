/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.LscTop.Dilate at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Limits
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.WeakStrong.Homothety

 















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.LscTop

 

 
def smulMetric (c : Set.Ioi (0 : ℝ)) (D : LSCMetric) : LSCMetric :=
  ⟨fun p => ENNReal.ofReal c * D p,
    ⟨fun x => by simp only [D.isExtMetric.1 x, mul_zero],
      fun x y h => D.isExtMetric.2.1 x y
        ((mul_eq_zero.1 h).resolve_left (ENNReal.ofReal_pos.2 c.2).ne'),
      fun x y => congrArg (ENNReal.ofReal c * ·) (D.isExtMetric.2.2.1 x y),
      fun x y z => by rw [← mul_add]; exact mul_le_mul_right (D.isExtMetric.2.2.2 x y z) _⟩,
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      D.lowerSemicontinuous fun _ _ h => mul_le_mul_right h _⟩

theorem smulMetric_apply (c : Set.Ioi (0 : ℝ)) (D : LSCMetric) (p : ℂ × ℂ) :
    smulMetric c D p = ENNReal.ofReal c * D p := rfl

 

 
end SupercriticalLQGUniqueness.B2.LscTop
