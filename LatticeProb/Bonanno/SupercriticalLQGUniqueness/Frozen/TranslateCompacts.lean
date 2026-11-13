/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.TranslateCompacts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.SLUMetricAPI

/-! Scratch freeze split of SLUField.lean:47. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

/-- The compact set `K + z`. -/
def translateCompacts (z : ℂ) (K : Compacts ℂ) : Compacts ℂ :=
  K.map (fun y => y + z) (by fun_prop)
end SupercriticalLQGUniqueness
