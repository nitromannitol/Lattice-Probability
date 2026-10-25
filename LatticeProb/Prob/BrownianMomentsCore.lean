module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Sources: BouRabeeGwynne/BrownianMoments.lean, BouRabeeGwynne/GaussianIncrementBounds.lean.
-/

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact fourth moments of Gaussian and Brownian increments

The centered real Gaussian law with variance `v` has fourth moment `3 v²`, proved from its
moment-generating function. The same identity transfers to the increments of the finite-dimensional
Brownian laws and to any process with those laws, giving the exponent-two increment estimate.
Markov's inequality then turns it into a tail bound for Gaussian increments. No existence of a
Brownian motion is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

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

/-- Fourth moment of the increment under the finite-dimensional Brownian Gaussian law
`BrownianReal.projectiveFamily I`, with the variance parameter converted to the Euclidean
time distance `|s - t|`. -/
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

/-- The fourth power of a centered real Gaussian is integrable for every variance,
including the degenerate variance-zero case. -/
theorem gaussianReal_integrable_fourth_power (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ ↦ x)
    (μ := gaussianReal 0 v) (by simp) 4

/-- The nonnegative fourth moment, in the extended nonnegative reals used by
Markov's inequality and Borel--Cantelli. -/
theorem gaussianReal_lintegral_abs_fourth (v : ℝ≥0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 4) ∂gaussianReal 0 v) =
      3 * (v : ℝ≥0∞) ^ 2 := by
  have habs (x : ℝ) : |x| ^ 4 = x ^ 4 := (by decide : Even 4).pow_abs x
  simp_rw [habs]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianReal_integrable_fourth_power v)
    (Filter.Eventually.of_forall fun x ↦ by positivity), gaussianReal_fourth_moment]
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow]

/-- Any random variable with the centered Gaussian law of variance `v` has nonnegative
fourth moment `3 v²` in the extended nonnegative reals. -/
theorem hasLaw_gaussian_lintegral_abs_fourth {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 4) ∂P) = 3 * (v : ℝ≥0∞) ^ 2 := by
  calc
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 4) ∂P) =
        ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 4) ∂gaussianReal 0 v := by
      exact hX.lintegral_comp (f := fun x : ℝ ↦ ENNReal.ofReal (|x| ^ 4)) (by fun_prop)
    _ = _ := gaussianReal_lintegral_abs_fourth v

/-- A centered Gaussian increment of variance `v` exceeds `r` in absolute
value with probability at most `3 v² / r⁴`. Degenerate variance is included. -/
theorem hasLaw_gaussian_measure_abs_ge_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) {r : ℝ} (hr : 0 < r) :
    P {ω | r ≤ |X ω|} ≤ 3 * (v : ℝ≥0∞) ^ 2 / ENNReal.ofReal (r ^ 4) := by
  have hmeas : AEMeasurable (fun ω ↦ ENNReal.ofReal (|X ω| ^ 4)) P := by
    fun_prop
  calc
    P {ω | r ≤ |X ω|} ≤
        P {ω | ENNReal.ofReal (r ^ 4) ≤ ENNReal.ofReal (|X ω| ^ 4)} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hr.le hω 4)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 4) ∂P) / ENNReal.ofReal (r ^ 4) :=
      meas_ge_le_lintegral_div hmeas (by positivity) ENNReal.ofReal_ne_top
    _ = _ := by rw [hasLaw_gaussian_lintegral_abs_fourth hX]

/-- The bound already applies to the finite-dimensional Brownian Gaussian laws
`BrownianReal.projectiveFamily I`, before a continuous Brownian process is available. -/
theorem brownianProjectiveFamily_measure_increment_ge_le
    (I : Finset ℝ≥0) (s t : I) {r : ℝ} (hr : 0 < r) :
    BrownianReal.projectiveFamily I {x | r ≤ |x s - x t|} ≤
      3 * (nndist s.1 t.1 : ℝ≥0∞) ^ 2 / ENNReal.ofReal (r ^ 4) :=
  hasLaw_gaussian_measure_abs_ge_le
    (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I s t).hasLaw hr

namespace BrownianMomentsCoreExample

/-- Nonvacuity: the standard Gaussian law `gaussianReal 0 1` has fourth moment `3`. -/
theorem standard_gaussian_fourth_moment :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  rw [gaussianReal_fourth_moment]
  norm_num

/-- Nonvacuity: the increment bound applies to any pre-Brownian process `B`, given as a
hypothesis `hB` on its finite-dimensional laws. -/
theorem preBrownian_increment_fourth_moment_apply {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, (B s ω - B t ω) ^ 4 ∂P) = 3 * |(s : ℝ) - (t : ℝ)| ^ 2 :=
  LatticeProb.preBrownian_increment_fourth_moment hB s t

/-- Nonvacuity: the tail bound applies to the increments of any pre-Brownian process `B`. -/
theorem preBrownian_increment_measure_ge_le_apply {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0)
    {r : ℝ} (hr : 0 < r) :
    P {ω | r ≤ |B s ω - B t ω|} ≤ 3 * (nndist s t : ℝ≥0∞) ^ 2 / ENNReal.ofReal (r ^ 4) :=
  LatticeProb.hasLaw_gaussian_measure_abs_ge_le (hB.hasLaw_sub s t) hr

end BrownianMomentsCoreExample

end LatticeProb
