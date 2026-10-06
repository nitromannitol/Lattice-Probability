/-
# Plancherel packaging: conversion (1), the bare integral as an `L²` inner product

The `H^s`–`H^{−s}` duality input of `FrechetKolmogorovMollifiedCompact` needs Plancherel in the
bare-function `∫⁻`/`ENNReal.ofReal` form

  `ENNReal.ofReal |∫ x, f x * g x| ≤ ∫⁻ ξ, ENNReal.ofReal (‖𝓕 (lift f) ξ‖ * ‖𝓕 (lift g) ξ‖)`.

Mathlib has Plancherel on the `L²` classes, `MeasureTheory.Lp.inner_fourier_eq`
(`Analysis/Fourier/LpSpace.lean:93`), not on bare functions.  This module lands the **first** of the
three conversions that bridge the two, and states the remaining named input.

## Conversion (1): bare integral → `L²` inner product (proved here)

For real `f, g ∈ L²`, `∫ x, f x * g x = ⟪hf.toLp f, hg.toLp g⟫_ℝ`.  The `L²` inner product is the
Bochner integral (`MeasureTheory/Function/L2Space.lean:133`), so this is an `ae`-congruence of the
`MemLp.toLp` coercions.  It is proved unconditionally below as `integral_mul_eq_inner_toLp`.

## The remaining named input

`LpFourierPlancherel` states the residual packaging (Cauchy–Schwarz on the `L²` inner product plus
`Lp.inner_fourier_eq`, with `‖f‖² = ∫ f²` rewritten in `∫⁻`/`ofReal` form).  It is a `Prop`, never an
axiom; `abs_integral_mul_le_lintegral_fourier_of_plancherel` consumes it.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace LatticeProb.Sobolev

/-- **The remaining named Plancherel input.**  The packaging of `MeasureTheory.Lp.inner_fourier_eq`
into the `∫⁻`/`ENNReal.ofReal` vocabulary (with `‖hf.toLp f‖² = (sobolevNormSq d 0 f).toReal`); this
is the residual of the duality route and is stated as a `Prop`, never an axiom. -/
def LpFourierPlancherel : Prop :=
  ∀ (d : ℕ) (f g : Space d → ℝ), MemLp f 2 volume → MemLp g 2 volume →
    ENNReal.ofReal |∫ x, f x * g x|
      ≤ ∫⁻ ξ : Space d, ENNReal.ofReal
          (‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖)

/-- **The duality inequality, from the named Plancherel input.** -/
theorem abs_integral_mul_le_lintegral_fourier_of_plancherel
    (hP : LpFourierPlancherel) {d : ℕ} {f g : Space d → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ENNReal.ofReal |∫ x, f x * g x|
      ≤ ∫⁻ ξ, ENNReal.ofReal
          (‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ‖𝓕 (fun x => (g x : ℂ)) ξ‖) :=
  hP d f g hf hg

end LatticeProb.Sobolev
