import Mathlib

/-!
# The one-dimensional continuous-time kernel

`lineKernel s k = (2π)⁻¹ ∫_{-π}^{π} e^{-s(1 - cos θ)} cos(kθ) dθ` is the kernel at
time `s` of the continuous-time simple random walk on `ℤ` that jumps at rate one, written
through its Fourier symbol `e^{-s(1 - cos θ)}`. This module proves the complex form of the
integral, the shift of the contour of integration to the line `Im θ = λ`, and the
exponential bound `|lineKernel s k| ≤ exp(-λk + s(cosh λ - 1))` that the shift gives. The
contour shift is the Cauchy-Goursat theorem on a rectangle, whose vertical sides cancel by
`2π`-periodicity. Nothing probabilistic is used: every statement is read off the integral.
-/

open MeasureTheory

noncomputable section

namespace LatticeProb.ContinuousTime

/-- The one-dimensional continuous-time kernel
`q_s(k) = (2π)⁻¹ ∫_{-π}^{π} e^{-s(1 - cos θ)} cos(kθ) dθ`. -/
def lineKernel (s : ℝ) (k : ℤ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in (-Real.pi)..Real.pi, Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ)

/-- The entire integrand `z ↦ e^{-s(1 - cos z) + ikz}` of the complex form of `lineKernel`. -/
def lineIntegrand (s : ℝ) (k : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (-(s : ℂ) * (1 - Complex.cos z) + (k : ℂ) * z * Complex.I)

/-! ### The complex form -/

/-- The complex integrand splits into a real exponential times `cos + i sin`. -/
private lemma lineIntegrand_eq (s : ℝ) (k : ℤ) (θ : ℝ) :
    lineIntegrand s k θ
      = (Real.exp (-s * (1 - Real.cos θ)) : ℂ)
          * ((Real.cos (k * θ) : ℂ) + (Real.sin (k * θ) : ℂ) * Complex.I) := by
  unfold lineIntegrand
  rw [Complex.exp_add]
  congr 1
  · rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · rw [show (k : ℂ) * (θ : ℂ) * Complex.I = ((k * θ : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The sine-weighted integrand integrates to zero on `[-π, π]` by oddness. -/
private lemma integral_exp_mul_sin_eq_zero (s : ℝ) (k : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi,
      Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ) = 0 := by
  let g : ℝ → ℝ := fun θ => Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ)
  have hodd : ∀ θ, g (-θ) = - g θ := by
    intro θ
    unfold g
    rw [Real.cos_neg]
    have hk : (k : ℝ) * (-θ) = -((k : ℝ) * θ) := by ring
    rw [hk, Real.sin_neg]
    ring
  have hcomp : (∫ θ in (-Real.pi)..Real.pi, g (-θ))
      = ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  have hneg : (∫ θ in (-Real.pi)..Real.pi, g (-θ))
      = - ∫ θ in (-Real.pi)..Real.pi, g θ := by
    simp_rw [hodd]
    simp
  have h2 : (∫ θ in (-Real.pi)..Real.pi, g θ)
      = - ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [← hneg, hcomp]
  linarith

/-- The kernel is `(2π)⁻¹` times the integral of the entire integrand over `[-π, π]`: the
sine part of `e^{ikθ}` integrates to zero because it is odd. -/
theorem lineKernel_eq_integral (s : ℝ) (k : ℤ) :
    (lineKernel s k : ℂ)
      = (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k θ := by
  have hpoint : ∀ θ : ℝ,
      lineIntegrand s k θ
        = ((Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ)
          + ((Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ) : ℝ) : ℂ)
              * Complex.I := by
    intro θ
    rw [lineIntegrand_eq]
    push_cast
    ring
  have hmain : (∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k θ)
      = ((∫ θ in (-Real.pi)..Real.pi,
            Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ) := by
    calc
      ∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k θ
          = ∫ θ in (-Real.pi)..Real.pi,
              (((Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ)
                + ((Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ) : ℝ) : ℂ)
                    * Complex.I) := by
            simp_rw [hpoint]
      _ = (∫ θ in (-Real.pi)..Real.pi,
              ((Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ))
            + ∫ θ in (-Real.pi)..Real.pi,
                (((Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ) : ℝ) : ℂ)
                  * Complex.I) := by
            rw [intervalIntegral.integral_add
              (Continuous.intervalIntegrable (by fun_prop) _ _)
              (Continuous.intervalIntegrable (by fun_prop) _ _)]
      _ = ((∫ θ in (-Real.pi)..Real.pi,
              Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ)
            + ((∫ θ in (-Real.pi)..Real.pi,
                Real.exp (-s * (1 - Real.cos θ)) * Real.sin (k * θ) : ℝ) : ℂ)
                * Complex.I := by
            rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
              intervalIntegral.integral_ofReal]
      _ = ((∫ θ in (-Real.pi)..Real.pi,
              Real.exp (-s * (1 - Real.cos θ)) * Real.cos (k * θ) : ℝ) : ℂ) := by
            rw [integral_exp_mul_sin_eq_zero]
            simp
  rw [lineKernel, hmain]
  push_cast
  ring

/-- `e^{k · 2πi} = 1` for every integer `k`. -/
private lemma exp_int_mul_two_pi_mul_I_eq_one (k : ℤ) :
    Complex.exp ((k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_int_mul]
  have h2 : Complex.exp ((2 * Real.pi : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I]
    simp
  rw [h2]
  simp

/-- The integrand is `2π`-periodic, because `k` is an integer. -/
theorem lineIntegrand_add_two_pi (s : ℝ) (k : ℤ) (z : ℂ) :
    lineIntegrand s k (z + 2 * Real.pi) = lineIntegrand s k z := by
  calc
    lineIntegrand s k (z + 2 * Real.pi)
        = Complex.exp ((-(s : ℂ) * (1 - Complex.cos z) + (k : ℂ) * z * Complex.I)
            + ((k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))) := by
          unfold lineIntegrand
          rw [Complex.cos_add_two_pi]
          congr 1
          ring
    _ = Complex.exp (-(s : ℂ) * (1 - Complex.cos z) + (k : ℂ) * z * Complex.I)
          * Complex.exp ((k : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
          rw [Complex.exp_add]
    _ = Complex.exp (-(s : ℂ) * (1 - Complex.cos z) + (k : ℂ) * z * Complex.I) := by
          rw [exp_int_mul_two_pi_mul_I_eq_one, mul_one]
    _ = lineIntegrand s k z := by
          rw [lineIntegrand]

/-- The integrand is an entire function. -/
theorem differentiable_lineIntegrand (s : ℝ) (k : ℤ) :
    Differentiable ℂ (lineIntegrand s k) := by
  unfold lineIntegrand
  fun_prop

/-! ### The contour shift and the exponential bound -/

/-- The contour of integration can be moved to the line `Im z = l`: Cauchy-Goursat on the
rectangle `[-π, π] × [0, l]`, whose two vertical sides cancel by periodicity. -/
theorem integral_lineIntegrand_shift (s : ℝ) (k : ℤ) (l : ℝ) :
    ∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k θ
      = ∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k (θ + l * Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (lineIntegrand s k)
    (-(Real.pi : ℂ)) ((Real.pi : ℂ) + l * Complex.I)
    ((differentiable_lineIntegrand s k).differentiableOn)
  have hvert : ∀ y : ℝ, lineIntegrand s k ((Real.pi : ℂ) + y * Complex.I)
      = lineIntegrand s k (-(Real.pi : ℂ) + y * Complex.I) := by
    intro y
    rw [← lineIntegrand_add_two_pi s k (-(Real.pi : ℂ) + y * Complex.I)]
    congr 1
    ring
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_mul, Complex.ofReal_zero] at h
  simp only [hvert, Complex.ofReal_neg, add_sub_cancel_right] at h
  exact sub_eq_zero.mp h

/-- The modulus of the integrand on the line `Im z = l` is
`exp(-s(1 - cos θ cosh l) - k l)`. -/
theorem norm_lineIntegrand_shift (s : ℝ) (k : ℤ) (θ l : ℝ) :
    ‖lineIntegrand s k (θ + l * Complex.I)‖
      = Real.exp (-s * (1 - Real.cos θ * Real.cosh l) - k * l) := by
  unfold lineIntegrand
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
    Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  ring

/-- The exponential bound `|q_s(k)| ≤ exp(-l k + s(cosh l - 1))`, for every real `l`, from
the shifted contour and `cos θ cosh l ≤ cosh l`. -/
theorem abs_lineKernel_le_exp {s : ℝ} (hs : 0 ≤ s) (k : ℤ) (l : ℝ) :
    |lineKernel s k| ≤ Real.exp (-(l * k) + s * (Real.cosh l - 1)) := by
  have hpi := Real.pi_pos
  have hbound : ∀ θ ∈ Set.uIoc (-Real.pi) Real.pi,
      ‖lineIntegrand s k (θ + l * Complex.I)‖
        ≤ Real.exp (-(l * k) + s * (Real.cosh l - 1)) := by
    intro θ _
    rw [norm_lineIntegrand_shift]
    apply Real.exp_le_exp.mpr
    have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h2 : 1 ≤ Real.cosh l := Real.one_le_cosh l
    have h3 : (0 : ℝ) ≤ Real.cosh l := by linarith
    nlinarith [mul_nonneg hs (mul_nonneg (sub_nonneg.mpr h1) h3)]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hq : |lineKernel s k| = (2 * Real.pi)⁻¹
      * ‖∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k (θ + l * Complex.I)‖ := by
    rw [← integral_lineIntegrand_shift, ← Real.norm_eq_abs, ← Complex.norm_real,
      lineKernel_eq_integral, norm_mul, norm_inv]
    congr 2
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hq]
  calc (2 * Real.pi)⁻¹
        * ‖∫ θ in (-Real.pi)..Real.pi, lineIntegrand s k (θ + l * Complex.I)‖
      ≤ (2 * Real.pi)⁻¹ * (Real.exp (-(l * k) + s * (Real.cosh l - 1))
          * |Real.pi - -Real.pi|) := by gcongr
    _ = Real.exp (-(l * k) + s * (Real.cosh l - 1)) := by
      rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity)]
      field_simp

/-- The kernel is at most one in absolute value. -/
theorem abs_lineKernel_le_one {s : ℝ} (hs : 0 ≤ s) (k : ℤ) : |lineKernel s k| ≤ 1 := by
  simpa using abs_lineKernel_le_exp hs k 0

/-- The kernel is continuous in the time. -/
theorem continuous_lineKernel (k : ℤ) : Continuous fun s => lineKernel s k := by
  unfold lineKernel
  apply Continuous.mul continuous_const
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

end LatticeProb.ContinuousTime
