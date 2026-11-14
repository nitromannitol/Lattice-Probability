/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CompactCrossLaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

def j1RoundCross (R : ℝ) : Set ℂ :=
  {z | dist z 0 ∈ Icc R (2 * R)}

theorem j1_round_cross_isCompact (R : ℝ) : IsCompact (j1RoundCross R) := by
  have hc : IsClosed (j1RoundCross R) := by
    exact isClosed_Icc.preimage (continuous_id.dist continuous_const)
  exact (isCompact_closedBall (0 : ℂ) (2 * R)).of_isClosed_subset hc
    (fun z hz => hz.2)

theorem j1_round_cross_scale_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ)
    (R : ℝ) (c : ℂ) (t : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ K
    let M : ℂ → ℂ := fun z => (r : ℂ) * z + c
    P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (M '' j1RoundCross R)
      (M '' sphere (0 : ℂ) R) (M '' sphere (0 : ℂ) (2 * R)) <
        ENNReal.ofReal r * t} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      (j1RoundCross R) (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) < t} :=
  j1_compact_cross_scale_law P W hW hKn ξ _ _ _
    (j1_round_cross_isCompact R) c t

end SupercriticalLQGUniqueness.B2.DG20Conc
