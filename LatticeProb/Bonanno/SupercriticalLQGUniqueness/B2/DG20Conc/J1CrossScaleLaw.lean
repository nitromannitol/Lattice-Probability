/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossScaleLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UnitCrossLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineCross

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_cross_scale_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ) (i : Bool) (c : ℂ)
    (t : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ K
    let F : ℂ → ℂ := fun z => (r : ℂ) * z + c
    P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (F '' laneCUnitUcross i)
      (F '' laneCUnitInner i) (F '' laneCUnitOuter i) <
        ENNReal.ofReal r * t} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) < t} := by
  dsimp only
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  have hr0 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hF : (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) =
      (fun z : ℂ => c + (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z) := by
    funext z
    exact add_comm _ _
  have hevent :
      {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' laneCUnitUcross i)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' laneCUnitInner i)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' laneCUnitOuter i) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * t} =
      {ω | crossLenIn ξ (fun z => phiMN W P K n
        (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
        (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) < t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hF]
    rw [j1_crossLen_image_affine ξ (fun z => phiMN W P K n z ω)
      (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) hr c]
    have hg : (fun z : ℂ => phiMN W P K n
        (c + (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z) ω) =
        (fun z : ℂ => phiMN W P K n
        ((((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) ω) := by
      funext z
      rw [add_comm]
    rw [hg]
    exact ENNReal.mul_lt_mul_iff_right hr0 hrt
  rw [hevent]
  exact j1_unit_cross_law P W hW hKn ξ i c measurableSet_Iio

end SupercriticalLQGUniqueness.B2.DG20Conc
