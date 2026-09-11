/-
Orthogonality of the characters of the circle, in the real form.

The `d`-dimensional local central limit theorem is read off the Fourier
representation of the kernel,

  `p_n(0, z) = (2π)^{-d} ∫_{[-π,π]^d} φ(θ)^n cos(θ · z) dθ`,   `φ(θ) = d^{-1} ∑_j cos θ_j`,

and that representation is proved without any Fourier theory: the right side
satisfies the same recursion as the kernel, and the base case `n = 0` is the
statement that the characters are orthogonal, `∫_{-π}^{π} cos(kθ) dθ = 0` for a
nonzero integer `k` and `2π` for `k = 0`.  That base case is what this file
proves.  The substitution `θ ↦ kθ` reduces it to `∫ cos = sin`, and both
endpoints vanish because the sine of an integer multiple of `π` is zero.
-/
import Mathlib

noncomputable section

namespace LatticeProb

open MeasureTheory intervalIntegral

/-- **Orthogonality of the characters**, the nonzero mode. -/
theorem integral_cos_int_mul (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * θ) = 0 := by
  have hck : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have h1 := intervalIntegral.integral_comp_mul_left (fun x => Real.cos x)
    (c := (k : ℝ)) (a := -Real.pi) (b := Real.pi) hck
  rw [h1, integral_cos]
  push_cast [Real.sin_int_mul_pi]
  simp

/-- **Orthogonality of the characters**, both modes at once: the integral of
`cos(kθ)` over a full period is `2π` at the trivial mode and `0` otherwise. -/
theorem integral_cos_int_mul_eq (k : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * θ)
      = if k = 0 then 2 * Real.pi else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
    ring
  · rw [if_neg hk]
    exact integral_cos_int_mul k hk

/-- **Orthogonality of the characters**, the nonzero mode, complex form: the
integral of `exp(i kθ)` over a full period vanishes for a nonzero integer `k`.
The substitution `θ ↦ kθ` reduces it to `∫ exp = 2 sin`, and both endpoints
vanish because the sine of an integer multiple of `π` is zero. -/
theorem integral_exp_int_mul_restrict (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * θ) * Complex.I) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos.le]
  have huIoc : Set.Ioc (-Real.pi) Real.pi = Set.uIoc (-Real.pi) Real.pi :=
    (Set.uIoc_of_le hle).symm
  rw [huIoc]
  have hiv : ∫ (t : ℝ) in -Real.pi..Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I)
      = ∫ (t : ℝ) in Set.uIoc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp [hle]
  rw [← hiv]
  have hkc : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (c := (k:ℝ)) (fun x => Complex.exp (x * Complex.I)) hkc]
  have hneg : (k:ℝ) * (-Real.pi) = -((k:ℝ) * Real.pi) := by ring
  rw [hneg, integral_exp_mul_I_eq_sin ((k:ℝ) * Real.pi)]
  rw [Real.sin_int_mul_pi]
  simp

/-- **Orthogonality of the characters**, both modes at once, complex form. -/
theorem integral_exp_int_mul_restrict_eq (k : ℤ) :
    ∫ θ in Set.Icc (-Real.pi) Real.pi,
        Complex.exp (Complex.ofReal ((k : ℝ) * θ) * Complex.I)
      = if k = 0 then 2 * Real.pi else 0 := by
  by_cases hk : k = 0
  · subst hk
    push_cast
    simp only [zero_mul, Complex.exp_zero]
    rw [MeasureTheory.integral_const]
    have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos.le]
    have hvol : (volume.restrict (Set.Icc (-Real.pi) Real.pi)) Set.univ
        = ENNReal.ofReal (2 * Real.pi) := by
      rw [Measure.restrict_apply (s := Set.Icc (-Real.pi) Real.pi) (t := Set.univ),
        Set.univ_inter, Real.volume_Icc]
      · congr 1
        ring
      · exact MeasurableSet.univ
    rw [Measure.real, hvol, ENNReal.toReal_ofReal]
    · simp
    · positivity
  · rw [if_neg hk]
    exact integral_exp_int_mul_restrict k hk

end LatticeProb
