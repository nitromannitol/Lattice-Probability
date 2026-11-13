/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsLFPPExponent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LfppCrossingLength

/-! Scratch freeze split of SLUField.lean:212. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `Q` is the LFPP distance exponent for `ξ` (DG (1.5), l. 330–333): `𝔞_ε = ε^{1 - ξQ + o(1)}`
as `ε → 0`, where `𝔞_ε` is a median of the LFPP left–right crossing distance of `[0,1]²`
(DG (1.4), l. 295–299) for the normalized whole-plane GFF (DG l. 280), computed from the
heat-kernel mollification `h*_ε = h * p_{ε²/2}` (DG (1.2), l. 284–288).

The predicate quantifies over every probability space carrying a normalized whole-plane GFF,
every continuous version `X ε` of `h*_ε` (for each `z`, almost surely `X ε z` is the limit of the
pairings of `h` with the truncated heat kernels `p_{ε²/2}(z - ·) χ_n`), and every choice `m ε` of
medians; no median or version is chosen. -/
def IsLFPPExponent (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P →
    ∀ (X : ℝ → Ω → C(ℂ, ℝ)) (m : ℝ → ℝ≥0∞),
      (∀ ε : ℝ, ∀ hε : 0 < ε,
        (∀ z : ℂ, ∀ᵐ ω ∂P,
          Tendsto (fun n : ℕ => h ω (positiveHeatTrunc ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n)) atTop
            (𝓝 (X ε ω z))) ∧
        IsMedian P (fun ω => lfppCrossingLength (ξ : ℝ) (X ε ω)) (m ε)) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q + δ)) ≤ m ε ∧ m ε ≤ ENNReal.ofReal (ε ^ (1 - (ξ : ℝ) * Q - δ))
end SupercriticalLQGUniqueness
