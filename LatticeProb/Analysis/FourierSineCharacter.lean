import Mathlib.Analysis.Fourier.AddCircle

/-! # Fourier characters and sine modes -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- Opposite characters on a circle of period `2 * θ` differ by the sine mode. -/
theorem fourier_neg_sub_fourier_eq_sine {θ : ℝ} (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (2 * θ)) - fourier n (x : AddCircle (2 * θ)) =
      -2 * Complex.I * (Real.sin (Real.pi * n * x / θ) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have hexp : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) /
      ((2 * θ : ℝ) : ℂ)) = ((Real.pi * n * x / θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hneg : (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) /
      ((2 * θ : ℝ) : ℂ)) = -((Real.pi * n * x / θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The difference of opposite Fourier coefficients is a symmetric sine integral. -/
theorem fourierCoeff_sub_neg_eq_sine_integral {θ : ℝ} [Fact (0 < 2 * θ)]
    (F : AddCircle (2 * θ) → ℂ) (n : ℤ)
    (hpos : IntervalIntegrable (fun x : ℝ => fourier (-n) (x : AddCircle (2 * θ)) * F x)
      volume (-θ) θ)
    (hneg : IntervalIntegrable (fun x : ℝ => fourier n (x : AddCircle (2 * θ)) * F x)
      volume (-θ) θ) :
    fourierCoeff F n - fourierCoeff F (-n) =
      (1 / (2 * θ) : ℝ) • ∫ x in (-θ)..θ,
        (-2 * Complex.I * (Real.sin (Real.pi * n * x / θ) : ℂ)) * F x := by
  rw [fourierCoeff_eq_intervalIntegral F n (-θ),
    fourierCoeff_eq_intervalIntegral F (-n) (-θ)]
  have hbound : -θ + 2 * θ = θ := by ring
  simp only [neg_neg, hbound, smul_eq_mul] at *
  rw [← smul_sub, ← intervalIntegral.integral_sub hpos hneg]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [← sub_mul, fourier_neg_sub_fourier_eq_sine]

end LatticeProb
