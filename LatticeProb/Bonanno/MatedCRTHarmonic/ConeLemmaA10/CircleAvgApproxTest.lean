/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CircleAvgApproxTest at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CompactTestRootMeasure

/-!
# Circle-average approximation tests under a compact root measure

This adapter rewrites the approximation's Lebesgue density integral as the same
circle-average density integrated against the finite root measure induced by a
nonnegative compactly supported test.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMSLemma27

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {H : ℝ → ℂ → Ω → ℝ} {γ : ℝ}

/-- Integrating the `k`th circle-average approximation against a test is the same as integrating
its pointwise `γ`-circle-average density against the corresponding compact root measure. -/
theorem approxTestIntegral_eq_compactTestRootMeasure_integral
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {f : ℂ → ℝ} (hf : Continuous f) (_hfc : HasCompactSupport f)
    (hf_nonneg : ∀ z, 0 ≤ f z) (k : ℕ) (ω : Ω) :
    approxTestIntegral (γ := γ) (H := H) f k ω =
      ∫ z, dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicRadius k) z ω)
        ∂compactTestRootMeasure f := by
  let r : ℝ := dyadicRadius k
  let d : ℂ → ℝ := fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * H r z ω)
  have hr : 0 < r := by
    dsimp [r]
    rw [MatedCRTHarmonic.GMCFacts.dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal (d z)) := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.mul
      (Real.continuous_exp.comp ((hH.continuous r hr ω).const_mul γ)).measurable
  have hApprox : approxTestIntegral (γ := γ) (H := H) f k ω =
      ∫ z, d z * f z := by
    rw [approxTestIntegral, lqgApprox,
      integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with z
      simp only [smul_eq_mul, d, r]
      rw [ENNReal.toReal_ofReal (by positivity)]
    · exact hd
    · exact Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top
  have hRoot := integral_compactTestRootMeasure_eq (f := f) (g := d) hf hf_nonneg
  calc
    approxTestIntegral (γ := γ) (H := H) f k ω = ∫ z, d z * f z := hApprox
    _ = ∫ z, f z * d z := by
      congr 1
      funext z
      ring
    _ = ∫ z, d z ∂compactTestRootMeasure f := hRoot.symm

end MatedCRTHarmonic.ConeLemmaA10

