/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_source_round_cross_scale_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n m : ℕ} (hKn : K ≤ n) (hmK : m ≤ K) (ξ : ℝ)
    (b : ℤ × ℤ) (t : ℝ≥0∞) :
    P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b)
      (LaneCInputs.sourceInner K m b) (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * t} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      (j1RoundCross ((2 : ℝ)^m))
      (sphere (0 : ℂ) ((2 : ℝ)^m))
      (sphere (0 : ℂ) (2 * (2 : ℝ)^m)) < t} := by
  have h := j1_round_cross_scale_law P W hW hKn ξ
    ((2 : ℝ)^m) (T20.dyCenter K b) t
  simpa only [j1_round_cross_image_source hmK b,
    j1_round_inner_image_source hmK b,
    j1_round_outer_image_source hmK b] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
