/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.TestTranslate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Support.HasCompactSupport_comp_sub

/-! Scratch freeze split of SLUField.lean:85. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

/-- `φ ↦ φ(· - z)` on `𝓓(ℂ)`, a continuous linear map (no case split: translations are
homeomorphisms for every `z`). -/
def testTranslate (z : ℂ) : TestC →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ
    (fun φ => ⟨fun x => φ (x - z), φ.contDiff.comp (contDiff_id.sub contDiff_const),
      hasCompactSupport_comp_sub z φ.hasCompactSupport, subset_univ _⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have : (fun φ : TestC => (⟨fun x => φ (x - z),
          φ.contDiff.comp (contDiff_id.sub contDiff_const),
          hasCompactSupport_comp_sub z φ.hasCompactSupport, subset_univ _⟩ : TestC)) ∘
          TestFunction.ofSupportedIn (subset_univ (K : Set ℂ)) =
          TestFunction.ofSupportedInCLM ℝ (subset_univ (translateCompacts z K : Set ℂ)) ∘
            testTranslateK z K := by
        funext φ; ext x; rfl
      rw [this]
      exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp (continuous_testTranslateK z K))
end SupercriticalLQGUniqueness
