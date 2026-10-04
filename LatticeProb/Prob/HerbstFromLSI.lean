/-
The Herbst argument: the Gaussian log-Sobolev inequality implies the exponential
moment bound for a Lipschitz functional.

`LatticeProb.GaussianLogSobolev n` bounds the entropy of a positive density with
`C`-Lipschitz logarithm by `C²/2`.  Applying it to the tilted density
`h_λ = exp(λ (f - ∫f)) / ∫ exp(λ (f - ∫f))`, whose logarithm is `λ f` up to a
constant and hence `λ L`-Lipschitz when `f` is `L`-Lipschitz, gives the
differential inequality `(d/dλ) log M(λ) ≤ λ L²` for the moment generating
function `M(λ) = ∫ exp(λ (f - ∫f))`.  Since `M(0) = 1`, integrating gives
`M(λ) ≤ exp(λ² L² / 2)`, which is `LatticeProb.GaussianHerbstBound n`.

This module proves the tilt, its positivity, its normalization and the
Lipschitz continuity of its logarithm: the three facts the entropy bound is
applied to.  The differential inequality `(log M)' ≤ λ L²` that follows, and
its integration from `M(0) = 1`, are the remaining step.

The argument is the classical one of Herbst (1975), as presented in Ledoux,
*The Concentration of Measure Phenomenon*, Section 5.1.
-/
import LatticeProb.External.GaussianLogSobolev
import LatticeProb.Prob.GaussianConcentration

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- The tilted density of the Herbst argument: `h_λ = exp(λ (f - ∫f)) / M(λ)`,
where `M(λ) = ∫ exp(λ (f - ∫f))` is the moment generating function of `f - ∫f`.
It is positive and integrates to `1`. -/
noncomputable def herbstTilt (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
    / ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- The tilted density is positive. -/
theorem herbstTilt_pos (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (hM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) :
    ∀ x, 0 < herbstTilt n f lam x := by
  intro x
  unfold herbstTilt
  exact div_pos (Real.exp_pos _) hM

/-- The tilted density integrates to `1`. -/
theorem herbstTilt_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (hM : ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≠ 0) :
    ∫ x, herbstTilt n f lam x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1 := by
  unfold herbstTilt
  rw [integral_div, div_self hM]

/-- The logarithm of the tilted density is `λ f` up to an additive constant, hence
`λ K`-Lipschitz when `f` is `K`-Lipschitz. -/
theorem herbstTilt_log_lipschitz (n : ℕ) (f : (Fin n → ℝ) → ℝ) (K lam : ℝ)
    (hK : 0 ≤ K) (lam0 : 0 ≤ lam) (hf : LipschitzWith ⟨K, hK⟩ f)
    (hM : 0 < ∫ x, Real.exp (lam * (f x - ∫ y, f y
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) :
    LipschitzWith ⟨lam * K, mul_nonneg lam0 hK⟩ (fun x => Real.log (herbstTilt n f lam x)) := by
  have hconst : ∀ x, Real.log (herbstTilt n f lam x)
      = lam * f x - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    intro x
    unfold herbstTilt
    rw [Real.log_div (Real.exp_ne_zero _) hM.ne', Real.log_exp]
    ring
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [hconst x, hconst y, Real.dist_eq]
  have hdiff : (lam * f x - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      - (lam * f y - lam * (∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        - Real.log (∫ x, Real.exp (lam * (f x - ∫ y, f y
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
      = lam * (f x - f y) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg lam0]
  have hd := hf.dist_le_mul x y
  rw [Real.dist_eq] at hd
  have hd' : |f x - f y| ≤ K * dist x y := hd
  calc lam * |f x - f y| ≤ lam * (K * dist x y) :=
        mul_le_mul_of_nonneg_left hd' lam0
    _ = (lam * K) * dist x y := by ring


end LatticeProb
