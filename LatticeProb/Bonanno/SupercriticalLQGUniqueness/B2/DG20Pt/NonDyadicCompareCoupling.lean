/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicCompareCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleCoupling

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem rpow_mul_dyadic (n : ℕ) (s : ℝ) :
    (2 : ℝ) ^ s * (2 : ℝ) ^ (-((n : ℝ) + s)) = (2 : ℝ)⁻¹ ^ n := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : s + -((n : ℝ) + s) = -(n : ℝ) := by ring
  rw [he, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

private theorem rpow_mul_inverse (s : ℝ) :
    (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) = 1 := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]

 


theorem dg20_non_dyadic_field_difference_coupled
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    let r : ℝ := (2 : ℝ) ^ s
    let W' := dg20ScaledNoise r (by positivity : 0 < r) W
    IsWhiteNoise P W' ∧
      ∀ᵐ ω ∂P, ∀ x : ℂ,
        phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 x ω -
          phiMN W P 0 n ((r : ℂ) * x) ω =
          phiVer W' P ((2 : ℝ) ^ (-s)) 1 x ω := by
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr : 0 < r := by dsimp [r]; positivity
  let W' := dg20ScaledNoise r hr W
  have hW' : IsWhiteNoise P W' := dg20_isWhiteNoise_scaled P W hW r hr
  refine ⟨hW', ?_⟩
  have hscale := dg20_phiVer_scaled_ae P W hW hr
    (show 0 < (2 : ℝ) ^ (-((n : ℝ) + s)) by positivity)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith :
        -((n : ℝ) + s) ≤ -s))
  have hadd := dg20_phi_real_band_add_ae P W' hW' n s hs
  filter_upwards [hscale, hadd] with ω hsc had x
  have hmul₁ : r * (2 : ℝ) ^ (-((n : ℝ) + s)) = (2 : ℝ)⁻¹ ^ n :=
    rpow_mul_dyadic n s
  have hmul₂ : r * (2 : ℝ) ^ (-s) = 1 := rpow_mul_inverse s
  have hhigh : phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s)))
      ((2 : ℝ) ^ (-s)) x ω = phiMN W P 0 n ((r : ℂ) * x) ω := by
    simpa only [hmul₁, hmul₂, phiMN, pow_zero] using hsc x
  rw [had x, hhigh]
  ring

end SupercriticalLQGUniqueness.B2.DG20Pt
