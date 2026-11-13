/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SLUFieldSupport at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent

 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun)

namespace IsWeakLQGMetric

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem measurable (h : IsWeakLQGMetric ξ Q D) :
    Measurable D := h.1

end IsWeakLQGMetric

end SupercriticalLQGUniqueness
