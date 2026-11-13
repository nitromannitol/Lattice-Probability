/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.GaussianIncrementBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Fourth-moment probability bounds for the actual Gaussian laws

These estimates are the finite-law input to the dyadic Borel--Cantelli
construction of continuous Brownian paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma gaussianReal_integrable_fourth_power (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ ↦ x)
    (μ := gaussianReal 0 v) (by simp) 4

/-- The nonnegative fourth moment, in the extended nonnegative reals used by
Markov's inequality and Borel--Cantelli. -/
lemma gaussianReal_lintegral_abs_fourth (v : ℝ≥0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ 4) ∂gaussianReal 0 v) =
      3 * (v : ℝ≥0∞) ^ 2 := by
  have habs (x : ℝ) : |x| ^ 4 = x ^ 4 := (by decide : Even 4).pow_abs x
  simp_rw [habs]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianReal_integrable_fourth_power v)
    (Filter.Eventually.of_forall fun x ↦ by positivity), gaussianReal_fourth_moment]
  simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, NNReal.coe_nonneg]

lemma hasLaw_gaussian_lintegral_abs_fourth {Ω : Type*} [MeasurableSpace Ω]
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

/-- The bound already applies to the actually constructed finite Gaussian laws,
before a continuous Brownian process is available. -/
theorem brownianProjectiveFamily_measure_increment_ge_le
    (I : Finset ℝ≥0) (s t : I) {r : ℝ} (hr : 0 < r) :
    BrownianReal.projectiveFamily I {x | r ≤ |x s - x t|} ≤
      3 * (nndist s.1 t.1 : ℝ≥0∞) ^ 2 / ENNReal.ofReal (r ^ 4) :=
  hasLaw_gaussian_measure_abs_ge_le
    (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I s t).hasLaw hr

end BouRabeeGwynne
