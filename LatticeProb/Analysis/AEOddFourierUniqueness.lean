import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Fourier uniqueness for almost-everywhere odd functions -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

variable {T : ℝ} [Fact (0 < T)]

/-- The Fourier coefficients of an almost-everywhere odd function are antisymmetric. -/
theorem fourierCoeff_neg_of_ae_odd (f : AddCircle T → ℂ)
    (hf : ∀ᵐ x ∂AddCircle.haarAddCircle, f (-x) = -f x) (n : ℤ) :
    fourierCoeff f (-n) = -fourierCoeff f n := by
  unfold fourierCoeff
  calc
    (∫ x, fourier (-(-n)) x • f x ∂AddCircle.haarAddCircle) =
        ∫ x, fourier (-(-n)) (-x) • f (-x) ∂AddCircle.haarAddCircle :=
      (integral_neg_eq_self _ _).symm
    _ = -(∫ x, fourier (-n) x • f x ∂AddCircle.haarAddCircle) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      simp only [hx, smul_neg, neg_inj]
      congr 1
      simp only [fourier_apply, neg_neg, zsmul_neg, neg_zsmul]

/-- An almost-everywhere odd square-integrable function is determined by its sine coefficients. -/
theorem ae_eq_zero_of_ae_odd_of_fourierCoeff_eq_neg (f : AddCircle T → ℂ)
    (hf : MemLp f 2 AddCircle.haarAddCircle)
    (hodd : ∀ᵐ x ∂AddCircle.haarAddCircle, f (-x) = -f x)
    (hsine : ∀ n : ℕ, fourierCoeff f (n : ℤ) =
      fourierCoeff f (-(n : ℤ))) :
    f =ᵐ[AddCircle.haarAddCircle] 0 := by
  have hz : ∀ n : ℤ, fourierCoeff f n = 0 := by
    have hnat (n : ℕ) : fourierCoeff f (n : ℤ) = 0 := by
      have h := hsine n
      rw [fourierCoeff_neg_of_ae_odd f hodd] at h
      linear_combination (1 / 2 : ℂ) * h
    intro n
    cases n with
    | ofNat n => exact hnat n
    | negSucc n =>
      change fourierCoeff f (-((n + 1 : ℕ) : ℤ)) = 0
      rw [fourierCoeff_neg_of_ae_odd f hodd, hnat (n + 1), neg_zero]
  have hLp : hf.toLp f = 0 := by
    apply fourierBasis.repr.injective
    ext n
    rw [fourierBasis_repr]
    have hcoeff := fourierCoeff_congr_ae hf.coeFn_toLp
    rw [hcoeff, hz]
    simp
  have := hf.coeFn_toLp
  rw [hLp] at this
  exact this.symm.trans (Lp.coeFn_zero ℂ 2 AddCircle.haarAddCircle)

end LatticeProb
