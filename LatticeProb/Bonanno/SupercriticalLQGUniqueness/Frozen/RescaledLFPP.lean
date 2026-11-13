/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.RescaledLFPP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LfppDistance

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `rescaledLFPP`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- The re-scaled LFPP metric `𝔞_ε⁻¹ D^ε_h` (DG l. 304, 326) for a positive normalizer `a` and a
continuous field `φ`, as a function `ℂ × ℂ → [-∞, ∞]` (the codomain of DG Definition 1.2). -/
def rescaledLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) : EReal :=
  ((ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p : ℝ≥0∞) : EReal)

end SupercriticalLQGUniqueness
