/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsCircleAverage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.TranslateDist

/-! Scratch freeze split of SLUField.lean:113. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `a` is the circle average `h_r(z)` of the distribution `h` (DG l. 572; Duplantier–Sheffield
§3.1): `a` is the limit, as `n → ∞`, of the average over the circle `∂B_r(z)` of the mollified
field `x ↦ ⟨h, ψ_{n,x}⟩`, where `ψ_{n,x} = LQGMetric.bumpTest n x` is the standard mollifier at
scale `2^{-n}` centred at `x`. The radius ranges over `r > 0` only (DS §3.1). The limit is unique
when it exists; no value is assigned when it does not. -/
def IsCircleAverage (h : DistC) (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.circleAverage (fun x => h (bumpTest n x)) z (r : ℝ)) atTop (𝓝 a)
end SupercriticalLQGUniqueness
