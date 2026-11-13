/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `IsLFPPNormalizer`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- `a` is the LFPP normalizing factor `𝔞_ε` (DG (1.4), l. 295–299): a median of the LFPP
left–right crossing distance of `[0,1]²` for the whole-plane GFF normalized by `h_1(0) = 0`
(DG l. 280), computed from the heat mollification `h*_ε` (DG (1.2)). As in the frozen
`IsLFPPExponent` (rulings J1/J2), the property is required for every probability space carrying
a normalized whole-plane GFF and every continuous version of `h*_ε`; no median, version or
realization is chosen. The carrier is the positive reals, the range of every such median. -/
def IsLFPPNormalizer (ξ ε : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ)) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P → ∀ X : Ω → C(ℂ, ℝ), IsHeatSmoothing P h ε X →
      IsMedian P (fun ω => lfppCrossingLength (ξ : ℝ) (X ω)) (ENNReal.ofReal (a : ℝ))

end SupercriticalLQGUniqueness
