/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.TestDilate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `testDilate`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- `φ ↦ φ((· - z)/r)` on `𝓓(ℂ)` for a positive radius `r` (DG l. 454–456): the test-function
side of the pullback `h ↦ h(r · + z)`. The carrier is `r > 0` only, so there is no zero-scale
branch; the body is the `r ≠ 0` construction of `LQGMetric.testAffinePull`, through the reused
`LQGMetric.affMap r z x = r⁻¹ • (x - z)`, `LQGMetric.affK` and `LQGMetric.pullK` (A6 at-use, `r > 0`). -/
def testDilate (r : Set.Ioi (0 : ℝ)) (z : ℂ) : TestC →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ
    (fun φ => ⟨φ ∘ LQGMetric.affMap (r : ℝ) z, LQGMetric.contDiff_comp_affMap (r : ℝ) z φ.contDiff,
      LQGMetric.hasCompactSupport_comp_affMap (r : ℝ) z (ne_of_gt r.2) φ.hasCompactSupport,
      subset_univ _⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have : (fun φ : TestC => (⟨φ ∘ LQGMetric.affMap (r : ℝ) z,
          LQGMetric.contDiff_comp_affMap (r : ℝ) z φ.contDiff,
          LQGMetric.hasCompactSupport_comp_affMap (r : ℝ) z (ne_of_gt r.2) φ.hasCompactSupport,
          subset_univ _⟩ : TestC)) ∘ TestFunction.ofSupportedIn (subset_univ (K : Set ℂ)) =
          TestFunction.ofSupportedInCLM ℝ (subset_univ (LQGMetric.affK (r : ℝ) z K : Set ℂ)) ∘
            LQGMetric.pullK (r : ℝ) z (ne_of_gt r.2) K := by
        funext φ; ext x; rfl
      rw [this]
      exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp
        (LQGMetric.continuous_pullK (r : ℝ) z (ne_of_gt r.2) K))

end SupercriticalLQGUniqueness
