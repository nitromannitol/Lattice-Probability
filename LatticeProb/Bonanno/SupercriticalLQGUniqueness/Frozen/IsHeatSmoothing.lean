/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `IsHeatSmoothing`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- `X` is a continuous version of the heat-kernel mollification `h*_ε = h * p_{ε²/2}` of the
random distribution `h` (DG (1.2), l. 284–288; l. 302 for a GFF plus a bounded continuous
function): for each `z`, almost surely `X ω z` is the limit of the pairings of `h ω` with the
truncated heat kernels `w ↦ p_{ε²/2}(z - w) χ_n(w)` (`positiveHeatTrunc`, positive time only).
This is the same version clause as in the frozen `IsLFPPExponent`; no version is chosen. -/
def IsHeatSmoothing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (ε : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ)) : Prop :=
  ∀ z : ℂ, ∀ᵐ ω ∂P,
    Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨(ε : ℝ) ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos ε.2 2) two_pos)⟩ z n)) atTop
      (𝓝 (X ω z))

end SupercriticalLQGUniqueness
