/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsTwoSidedTight at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF

/-! Scratch freeze split of SLUField.lean:130. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- The `[0,∞]`-valued random variables `X i` and their reciprocals are tight: for every `ε > 0`
there is a real `M > 0` such that, for every `i`, `P{X i > M} ≤ ε` and `P{X i < M⁻¹} ≤ ε`.
The `X i` are random variables (almost everywhere measurable). (This forces `0 < X i < ∞`
almost surely; this is equivalent to tightness of the laws of the real
random variables `X i` and `1 / X i`.) -/
def IsTwoSidedTight {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ≥0∞) :
    Prop :=
  (∀ i : ι, AEMeasurable (X i) P) ∧
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ i : ι,
    P {ω | ENNReal.ofReal M < X i ω} ≤ ENNReal.ofReal ε ∧
      P {ω | X i ω < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ε
end SupercriticalLQGUniqueness
