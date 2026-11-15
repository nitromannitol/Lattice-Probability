import LatticeProb.Analysis.OddLiftFourierIntegrability
import LatticeProb.Analysis.AEOddFourierUniqueness

/-! # Sine coefficients on an interval -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- The Fourier coefficient difference of an odd lift is its positive-interval sine pairing. -/
theorem fourierCoeff_sub_neg_oddLift_eq_sine {θ : ℝ} [Fact (0 < 2 * θ)]
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo 0 θ))) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) n -
        fourierCoeff (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) (-n) =
      ((-2 * Complex.I) / θ) * ∫ x in (0 : ℝ)..θ,
        (Real.sin (Real.pi * n * x / θ) : ℂ) * f x := by
  have hθ : 0 < θ := by linarith [Fact.out (p := 0 < 2 * θ)]
  let g : ℝ → ℂ := fun x => (Real.sin (Real.pi * n * x / θ) : ℂ) *
    oddIntervalExtension f x
  have hg : IntervalIntegrable g volume (-θ) θ := by
    have hf' : IntervalIntegrable (oddIntervalExtension f) volume (-θ) θ := by
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2
      exact (memLp_oddIntervalExtension hθ hf).integrable (by norm_num)
    exact hf'.continuousOn_mul (by fun_prop)
  have heven : ∀ x, g (-x) = g x := by
    intro x
    dsimp [g]
    have harg : Real.pi * (n : ℝ) * -x / θ = -(Real.pi * n * x / θ) := by ring
    rw [harg, Real.sin_neg, Complex.ofReal_neg, oddIntervalExtension_neg]
    ring
  have hleft : IntervalIntegrable g volume (-θ) 0 :=
    hg.mono_set (by simp only [uIcc_of_le (by linarith : -θ ≤ θ),
      uIcc_of_le (by linarith : -θ ≤ (0 : ℝ))]; exact Icc_subset_Icc le_rfl (le_of_lt hθ))
  have hright : IntervalIntegrable g volume 0 θ :=
    hg.mono_set (by simp only [uIcc_of_le (by linarith : -θ ≤ θ),
      uIcc_of_le (le_of_lt hθ)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hreflect : (∫ x in (-θ)..0, g x) = ∫ x in (0 : ℝ)..θ, g x := by
    calc
      (∫ x in (-θ)..0, g x) = ∫ x in (0 : ℝ)..θ, g (-x) := by
        simp only [intervalIntegral.integral_comp_neg, neg_zero]
      _ = ∫ x in (0 : ℝ)..θ, g x := by simp only [heven]
  have hsplit : (∫ x in (-θ)..θ, g x) = 2 * ∫ x in (0 : ℝ)..θ, g x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright, hreflect]
    ring
  have hpos : (∫ x in (0 : ℝ)..θ, g x) = ∫ x in (0 : ℝ)..θ,
      (Real.sin (Real.pi * n * x / θ) : ℂ) * f x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hθ)
    intro x hx
    simp only [g, oddIntervalExtension_of_pos f hx.1]
  rw [fourierCoeff_sub_neg_oddLift hf n]
  have hconv : (∫ x in (-θ)..θ,
      (-2 * Complex.I * (Real.sin (Real.pi * n * x / θ) : ℂ)) *
        AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f) x) =
      (-2 * Complex.I) * ∫ x in (-θ)..θ, g x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro x hx
    have hx' : x ∈ Ioc (-θ) (-θ + 2 * θ) := by constructor <;> linarith [hx.1, hx.2]
    dsimp only
    rw [AddCircle.liftIoc_coe_apply hx']
    dsimp [g]
    ring
  rw [hconv, hsplit, hpos]
  clear hconv hsplit hpos hreflect hleft hright heven hg g hf
  generalize (∫ x in (0 : ℝ)..θ, (Real.sin (Real.pi * n * x / θ) : ℂ) * f x) = z
  simp only [Algebra.smul_def]
  change ((1 / (2 * θ) : ℝ) : ℂ) * ((-2 * Complex.I) * (2 * z)) =
    ((-2 * Complex.I) / θ) * z
  push_cast
  have hθc : (θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hθ)
  field_simp [hθc]

end LatticeProb
