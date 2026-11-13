/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsMedian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric

/-! Scratch freeze split of SLUField.lean:172. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `m` is a median of the `[0,∞]`-valued random variable `L` (almost everywhere measurable)
under `P`. -/
def IsMedian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : Ω → ℝ≥0∞) (m : ℝ≥0∞) :
    Prop :=
  AEMeasurable L P ∧ 2⁻¹ ≤ P {ω | L ω ≤ m} ∧ 2⁻¹ ≤ P {ω | m ≤ L ω}
end SupercriticalLQGUniqueness
