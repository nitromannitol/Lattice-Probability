/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineAround
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem j1_block_around_le
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ) (i : Bool) (v : ℂ) (ω : Ω) :
    (lfppContMetric ξ (fun z => phiMN W P K n z ω)
      ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
      (laneBBlockAround i v K) (j1BlockInner i v K)
      (j1BlockOuter i v K) ≤
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      (lfppContMetric ξ (fun z => phiMN W P K n
        (((2 : ℝ)⁻¹ ^ K : ℝ) * z + j1BlockAffineCenter v K) ω)
        ((isPhiVersion_phiMN hW hKn).cont ω |>.comp
          (show Continuous (fun z : ℂ =>
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + j1BlockAffineCenter v K)) by
              fun_prop))).aroundDist
          (laneCUnitUaround i) (laneCUnitInner i)
          (laneCUnitOuter i) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ K
  let c := j1BlockAffineCenter v K
  have hr : 0 < r := by dsimp [r]; positivity
  have hF : (fun z : ℂ => c + (r : ℂ) * z) =
      (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) := by
    funext z
    simp only [c, r, j1BlockAffineCenter, Complex.real_smul]
    ring
  have hh := j1_aroundDist_image_affine_le ξ
    (fun z => phiMN W P K n z ω)
    ((isPhiVersion_phiMN hW hKn).cont ω)
    (laneCUnitUaround i) (laneCUnitInner i) (laneCUnitOuter i)
    hr c
  simp only [laneBBlockAround, j1BlockInner, j1BlockOuter, ← hF]
  simpa only [r, c, add_comm] using hh

end SupercriticalLQGUniqueness.B2.DG20Conc
