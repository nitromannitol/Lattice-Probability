/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CompactCrossLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1AffineCross
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFieldScale

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_compact_cross_scale_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {K n : ℕ} (hKn : K ≤ n) (ξ : ℝ)
    (U E F : Set ℂ) (hU : IsCompact U) (c : ℂ) (t : ℝ≥0∞) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ K
    let M : ℂ → ℂ := fun z => (r : ℂ) * z + c
    P {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (M '' U) (M '' E) (M '' F) < ENNReal.ofReal r * t} =
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 (n - K) z ω)
      U E F < t} := by
  dsimp only
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  have hr0 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hM : (fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) =
      (fun z : ℂ => c + (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z) := by
    funext z
    exact add_comm _ _
  have hevent :
      {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' U)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' E)
        ((fun z : ℂ => (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) '' F) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) * t} =
      {ω | crossLenIn ξ (fun z => phiMN W P K n
        (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω) U E F < t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hM]
    rw [j1_crossLen_image_affine ξ (fun z => phiMN W P K n z ω) U E F hr c]
    have hg : (fun z : ℂ => phiMN W P K n
        (c + (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z) ω) =
        (fun z : ℂ => phiMN W P K n
        ((((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * z + c) ω) := by
      funext z
      rw [add_comm]
    rw [hg]
    exact ENNReal.mul_lt_mul_iff_right hr0 hrt
  rw [hevent]
  have hφ := isPhiVersion_phiMN hW hKn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - K))
  have hc : Continuous (fun z : ℂ =>
      (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) := by fun_prop
  apply measure_crossLenIn_eq hU
    (fun ω => (hφ.cont ω).comp hc)
    (fun z => hφ.meas _)
    hφ0.cont hφ0.meas
    ?_ measurableSet_Iio
  simpa only [Function.comp_def, Circle.coe_one, one_mul, add_comm] using
    laneB_fine_field_scale_motion P W hW hKn (1 : Circle) c

end SupercriticalLQGUniqueness.B2.DG20Conc
