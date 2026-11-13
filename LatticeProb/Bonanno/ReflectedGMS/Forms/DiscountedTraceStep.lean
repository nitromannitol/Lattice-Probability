/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DiscountedTraceStep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Discounted finite-target steps of the actual reflected process

The joint law of the first holding time and the next finite-target step is
already proved in `ReflectedWalk`. Integrating that law gives its exact Laplace
kernel. The transition outside the target remains the full-energy harmonic
measure in `G.transProb`; it is not replaced by killing at a cutoff.

The discount below uses the first holding time at the starting vertex. Outside
the finite target this differs from the entire excursion duration. This is the
clock used in the existing approximating-chain construction.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.DiscountedTraceStep

private theorem discounted_exponentialPDF {r α : ℝ} (hr : 0 < r) (hα : 0 ≤ α) (s : ℝ) :
    exponentialPDF r s * ENNReal.ofReal (Real.exp (-α * s)) =
      ENNReal.ofReal (r / (r + α)) * exponentialPDF (r + α) s := by
  by_cases hs : 0 ≤ s
  · have hra : 0 < r + α := add_pos_of_pos_of_nonneg hr hα
    rw [exponentialPDF_of_nonneg hs, exponentialPDF_of_nonneg hs,
      ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_nonneg _)),
      ← ENNReal.ofReal_mul (div_nonneg hr.le hra.le)]
    congr 1
    calc
      r * Real.exp (-(r * s)) * Real.exp (-α * s) =
          r * Real.exp (-((r + α) * s)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ = r / (r + α) * ((r + α) * Real.exp (-((r + α) * s))) := by
        field_simp [hra.ne']
  · simp only [exponentialPDF_of_neg (lt_of_not_ge hs), zero_mul, mul_zero]

/-- The exponential Laplace transform, using the existing density normalization. -/
theorem lintegral_expMeasure_discount {r α : ℝ} (hr : 0 < r) (hα : 0 ≤ α) :
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-α * s)) ∂ProbabilityTheory.expMeasure r) =
      ENNReal.ofReal (r / (r + α)) := by
  have hp (q : ℝ) : Measurable (exponentialPDF q) :=
    (measurable_exponentialPDFReal q).ennreal_ofReal
  have hf : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-α * s))) := by fun_prop
  change (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-α * s))
    ∂volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (hp r) hf]
  simp only [Pi.mul_apply, discounted_exponentialPDF hr hα]
  rw [lintegral_const_mul _ (hp (r + α)),
    lintegral_exponentialPDF_eq_one (add_pos_of_pos_of_nonneg hr hα), mul_one]

private theorem map_expMeasure_toReal {r : ℝ} (hr : 0 < r) :
    ((ProbabilityTheory.expMeasure r).map ReflectedWalk.Theorem16.toWithTop).map
      (fun s : WithTop ℝ≥0 => ENNReal.toReal s) = ProbabilityTheory.expMeasure r := by
  ext B hB
  rw [Measure.map_apply (show Measurable (fun s : WithTop ℝ≥0 => ENNReal.toReal s) from
    ENNReal.measurable_toReal) hB]
  exact ReflectedWalk.Theorem16.map_toWithTop_expMeasure_toReal_preimage hr hB

open ReflectedWalk ReflectedWalk.Theorem16

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]
  {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer} {𝓧 : ProcessFamily V}

end ReflectedGMS.DiscountedTraceStep
