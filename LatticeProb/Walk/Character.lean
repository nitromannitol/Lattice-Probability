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

end LatticeProb
