/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsCircleAverage

/-! Scratch freeze split of SLUField.lean:119. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `h` is a whole-plane GFF normalized so that its average over the unit circle is zero
(DG l. 280): a whole-plane GFF (`LQGMetric.IsWholePlaneGFF`, covariance `-log|x - y|` against
mean-zero test functions) with `h_1(0) = 0` almost surely. -/
def IsNormalizedWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistC)
    (P : Measure Ω) : Prop :=
  IsWholePlaneGFF h P ∧ ∀ᵐ ω ∂P, IsCircleAverage (h ω) ⟨1, Set.mem_Ioi.mpr one_pos⟩ 0 0
end SupercriticalLQGUniqueness
