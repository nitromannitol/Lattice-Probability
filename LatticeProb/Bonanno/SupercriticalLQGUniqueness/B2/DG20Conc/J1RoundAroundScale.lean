/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundAroundScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundAroundShape
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAround

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem j1_source_round_around_le
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n m : ℕ} (hKn : K ≤ n) (hmK : m ≤ K)
    (ξ : ℝ) (b : ℤ × ℤ) (ω : Ω) :
    (lfppContMetric ξ (fun z => phiMN W P K n z ω)
      ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) ≤
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      (lfppContMetric ξ (fun z => phiMN W P K n
        (((2 : ℝ)⁻¹ ^ K : ℝ) * z + T20.dyCenter K b) ω)
        ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
          (show Continuous (fun z : ℂ =>
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + T20.dyCenter K b)) by
              fun_prop))).aroundDist
          {z : ℂ | (2 : ℝ)^m < dist z 0 ∧
            dist z 0 < 2 * (2 : ℝ)^m}
          (Metric.sphere (0 : ℂ) ((2 : ℝ)^m))
          (Metric.sphere (0 : ℂ) (2 * (2 : ℝ)^m)) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ K
  let c := T20.dyCenter K b
  have hh := j1_aroundDist_image_affine_le ξ
    (fun z => phiMN W P K n z ω)
    ((isPhiVersion_phiMN hW hKn).cont ω)
    {z : ℂ | (2 : ℝ)^m < dist z 0 ∧
      dist z 0 < 2 * (2 : ℝ)^m}
    (Metric.sphere (0 : ℂ) ((2 : ℝ)^m))
    (Metric.sphere (0 : ℂ) (2 * (2 : ℝ)^m))
    (by dsimp [r]; positivity : 0 < r) c
  have hU : (fun z : ℂ => c + (r : ℂ) * z) ''
      {z : ℂ | (2 : ℝ)^m < dist z 0 ∧
        dist z 0 < 2 * (2 : ℝ)^m} =
      LaneCInputs.sourceAround K m b := by
    convert j1_round_around_image_source hmK b using 1 <;>
      simp only [r, c, add_comm]
  have hE : (fun z : ℂ => c + (r : ℂ) * z) ''
      Metric.sphere (0 : ℂ) ((2 : ℝ)^m) =
      LaneCInputs.sourceInner K m b := by
    convert j1_round_inner_image_source hmK b using 1 <;>
      simp only [r, c, add_comm]
  have hF : (fun z : ℂ => c + (r : ℂ) * z) ''
      Metric.sphere (0 : ℂ) (2 * (2 : ℝ)^m) =
      LaneCInputs.sourceOuter K m b := by
    convert j1_round_outer_image_source hmK b using 1 <;>
      simp only [r, c, add_comm]
  rw [hU, hE, hF] at hh
  simpa only [r, c, add_comm] using hh

end SupercriticalLQGUniqueness.B2.DG20Conc
