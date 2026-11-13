/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic.Ring

/-!
# Exact fourth moments for the Brownian finite-dimensional laws

These are proved from the moment-generating function of the actual real
Gaussian distribution. They provide the exponent-two increment estimate used
in a continuous-modification construction; no Brownian existence is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BouRabeeGwynne

private lemma gaussianExp_hasDerivAt (v t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (v * x ^ 2 / 2))
      (v * t * Real.exp (v * t ^ 2 / 2)) t := by
  convert! ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2).exp using 1
  simp only [Pi.pow_apply, id_eq]
  ring

private lemma gaussianExp_first_hasDerivAt (v t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ v * x * Real.exp (v * x ^ 2 / 2))
      ((v + v ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2)) t := by
  convert! ((hasDerivAt_id t).const_mul v).mul (gaussianExp_hasDerivAt v t)
    using 1
  simp only [id_eq]
  ring

private lemma gaussianExp_second_hasDerivAt (v t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (v + v ^ 2 * x ^ 2) * Real.exp (v * x ^ 2 / 2))
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (v * t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun x : ℝ ↦ v + v ^ 2 * x ^ 2) (2 * v ^ 2 * t) t := by
    convert! (hasDerivAt_const t v).add (((hasDerivAt_id t).pow 2).const_mul (v ^ 2))
      using 1
    simp only [id_eq]
    ring
  convert! hp.mul (gaussianExp_hasDerivAt v t) using 1
  ring

private lemma gaussianExp_third_hasDerivAt (v t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (3 * v ^ 2 * x + v ^ 3 * x ^ 3) *
      Real.exp (v * x ^ 2 / 2))
      ((3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) *
        Real.exp (v * t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun x : ℝ ↦ 3 * v ^ 2 * x + v ^ 3 * x ^ 3)
      (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t := by
    convert! ((hasDerivAt_id t).const_mul (3 * v ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (v ^ 3)) using 1
    simp only [id_eq]
    ring
  convert! hp.mul (gaussianExp_hasDerivAt v t) using 1
  ring

/-- The centered real Gaussian with variance `v` has fourth moment `3 * v²`,
including the degenerate variance-zero case. -/
theorem gaussianReal_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
      symm
      simpa using (iteratedDeriv_mgf_zero
        (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 v) (by simp) 4)
    _ = 3 * (v : ℝ) ^ 2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
        funext (fun t ↦ (gaussianExp_hasDerivAt (v : ℝ) t).deriv),
        funext (fun t ↦ (gaussianExp_first_hasDerivAt (v : ℝ) t).deriv),
        funext (fun t ↦ (gaussianExp_second_hasDerivAt (v : ℝ) t).deriv),
        (gaussianExp_third_hasDerivAt (v : ℝ) 0).deriv]
      simp

/-- Fourth moment of the increment under an actual finite-dimensional Brownian
Gaussian law, with the variance parameter converted to Euclidean time distance. -/
theorem brownianProjectiveFamily_increment_fourth_moment (I : Finset ℝ≥0) (s t : I) :
    (∫ x : I → ℝ, (x s - x t) ^ 4 ∂BrownianReal.projectiveFamily I) =
      3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
  calc
    (∫ x : I → ℝ, (x s - x t) ^ 4 ∂BrownianReal.projectiveFamily I) =
        ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (nndist s.1 t.1) := by
      simpa only [Function.comp_def] using
        (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I s t).hasLaw.integral_comp
          (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
    _ = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
      rw [gaussianReal_fourth_moment]
      rfl

/-- Any process with the Brownian finite-dimensional laws inherits the exact
fourth-moment increment estimate. This transfer does not assert its existence. -/
theorem preBrownian_increment_fourth_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, (B s ω - B t ω) ^ 4 ∂P) = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
  calc
    (∫ ω, (B s ω - B t ω) ^ 4 ∂P) =
        ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (nndist s.1 t.1) := by
      simpa only [Function.comp_def, Pi.sub_apply] using
        (hB.hasLaw_sub s t).integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
    _ = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 := by
      rw [gaussianReal_fourth_moment, coe_nndist, Real.dist_eq]
      rfl

end BouRabeeGwynne
