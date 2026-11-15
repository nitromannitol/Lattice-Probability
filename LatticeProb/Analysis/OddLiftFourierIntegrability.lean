import LatticeProb.Analysis.OddIntervalCircle
import LatticeProb.Analysis.FourierSineCharacter

/-! # Integrability of Fourier coefficients of an odd interval lift -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Fourier-character pullbacks of the odd lift of an interval L² function are integrable. -/
theorem intervalIntegrable_fourier_mul_oddLift {θ : ℝ} [Fact (0 < 2 * θ)]
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo 0 θ))) (n : ℤ) :
    IntervalIntegrable (fun x : ℝ => fourier n (x : AddCircle (2 * θ)) *
      AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) x) volume (-θ) θ := by
  have hθ : 0 < θ := by linarith [Fact.out (p := 0 < 2 * θ)]
  have hle : -θ ≤ θ := by linarith
  have hg : IntervalIntegrable (oddIntervalExtension f) volume (-θ) θ := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).2
    exact (memLp_oddIntervalExtension hθ hf).integrable (by norm_num)
  have hF : IntervalIntegrable
      (fun x : ℝ => AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) x)
      volume (-θ) θ := by
    apply (intervalIntegrable_congr_uIoo ?_).2 hg
    intro x hx
    have hx' : x ∈ Ioc (-θ) (-θ + 2 * θ) := by
      rw [uIoo_of_le hle] at hx
      constructor <;> linarith [hx.1, hx.2]
    exact AddCircle.liftIoc_coe_apply hx'
  exact hF.continuousOn_mul
    (((map_continuous (fourier n)).comp (AddCircle.continuous_mk' _)).continuousOn)

/-- The Fourier-coefficient difference of an odd lift has a symmetric sine integral. -/
theorem fourierCoeff_sub_neg_oddLift {θ : ℝ} [Fact (0 < 2 * θ)]
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo 0 θ))) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) n -
        fourierCoeff (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) (-n) =
      (1 / (2 * θ) : ℝ) • ∫ x in (-θ)..θ,
        (-2 * Complex.I * (Real.sin (Real.pi * n * x / θ) : ℂ)) *
          AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) x := by
  exact fourierCoeff_sub_neg_eq_sine_integral _ n
    (intervalIntegrable_fourier_mul_oddLift hf (-n))
    (intervalIntegrable_fourier_mul_oddLift hf n)

end LatticeProb
