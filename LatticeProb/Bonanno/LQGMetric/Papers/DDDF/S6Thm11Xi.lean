/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm11Xi at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamMean
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

/-!
# `ξ = γ/d_γ < 2` and DDDF Prop 27 without it (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1345 uses `ξ < 2`. From the proved `χ ≤ 2`
(`DG.chiLeTwo`) one gets `d_γ ≥ 1` (`DG.one_le_dGamma`), hence `ξ = γ/d_γ ≤ γ < 2` (as in
`S6.s6_conditionT_psiQ₁`). `s6_diam_mean'` is `S6D.s6_diam_mean` with that hypothesis discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E Blueprint WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `ξ = γ/d_γ < 2` for `γ ∈ (0,2)` (`d_γ ≥ 1` from `χ ≤ 2`) -/
lemma xiGamma_lt_two {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : xiGamma γ < 2 := by
  have hd := DG.one_le_dGamma DG.chiLeTwo hγ hγ2
  have : xiGamma γ ≤ γ := div_le_self hγ.le hd
  linarith

end S6D
end DDDF
end LQGMetric
