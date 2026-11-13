/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Support.Continuous_testTranslateK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.TestTranslateK

 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

theorem continuous_testTranslateK (z : ℂ) (K : Compacts ℂ) :
    Continuous (testTranslateK z K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  have hA : Continuous fun x : ℂ => x - z := by fun_prop
  have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ testTranslateK z K) =
      (fun g => g.compContinuous ⟨fun x : ℂ => x - z, hA⟩) ∘
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext φ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [BoundedContinuousFunction.compContinuous_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_comp_sub i z x
  rw [key]
  exact (BoundedContinuousFunction.continuous_compContinuous _).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous
end SupercriticalLQGUniqueness
