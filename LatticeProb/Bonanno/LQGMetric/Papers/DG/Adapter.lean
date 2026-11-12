/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Adapter at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Blueprint
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Adapter: DG Theorem 1.5 gives LQGDimension's LFPP exponent (node DIM.L-LD-exponent)

Decision D12 = `decisions/DEC-A.md` D-A1, step 4: `λ = 1 − 2/d_γ − γ²/(2d_γ)` is an LFPP exponent at
`ξ = γ/d_γ` in the sense of `LQGDimension.IsLFPPExponent` (paths `[0,1] → U = (−2,2)²` from `0`
to `1`). Lower bound from DG (1.5a) (`D(0,1) ≤ D_LD(0,1)`, more paths), upper bound from DG (1.5b)
with `U' = B_1(1/2)` and `K = {0,1}` (paths in `closure U' ⊂ U`, so `D_LD(0,1) ≤ D(0,1;U')`).
"`D = δ^{λ+o(1)}` w.p. → 1" then gives `log D / log δ → λ` in probability. DEC-A's own sandwich
argument (no published proof of this bookkeeping step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

lemma lfppLength_nonneg (ξ : ℝ) (φ : ℂ → ℝ) (p : ℝ → ℂ) :
    0 ≤ LQGDimension.lfppLength ξ φ p :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

lemma bddBelow_dg (ξ : ℝ) (φ : ℂ → ℝ) (S : Set ℂ) (z w : ℂ) :
    BddBelow (range fun p : {p : ℝ → ℂ // IsDGPath S z w p} =>
      LQGDimension.lfppLength ξ φ p.1) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; exact lfppLength_nonneg ξ φ q.1⟩
