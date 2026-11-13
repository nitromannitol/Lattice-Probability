/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CompactTestRootMeasure at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaTestL1
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CompactSupportMargin

/-!
# Finite root measures from compact test functions

For a nonnegative compactly supported test function, its Lebesgue-weighted root law is a finite
measure concentrated on the test's topological support. The two density integration formulas
below are the conversion steps used when a root-coordinate integral is rewritten as a test
integral against a GMC approximation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

/-- The finite root-coordinate measure associated with a nonnegative test function. -/
def compactTestRootMeasure (f : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (f z))

lemma measurable_compactTestRootDensity {f : ℂ → ℝ} (hf : Continuous f) :
    Measurable (fun z : ℂ => ENNReal.ofReal (f z)) :=
  ENNReal.measurable_ofReal.comp hf.measurable

/-- Its total mass is the ordinary integral of the test function. -/
theorem compactTestRootMeasure_univ_eq_integral {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hf_nonneg : ∀ z, 0 ≤ f z) :
    compactTestRootMeasure f Set.univ = ENNReal.ofReal (∫ z, f z) := by
  have hi : Integrable f (volume : Measure ℂ) := hf.integrable_of_hasCompactSupport hfc
  rw [compactTestRootMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf_nonneg)).symm

/-- A continuous nonnegative compactly supported test gives a finite root-coordinate measure. -/
theorem isFiniteMeasure_compactTestRootMeasure {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hf_nonneg : ∀ z, 0 ≤ f z) :
    IsFiniteMeasure (compactTestRootMeasure f) := by
  have hmass : compactTestRootMeasure f Set.univ < ⊤ := by
    rw [compactTestRootMeasure_univ_eq_integral hf hfc hf_nonneg]
    exact ENNReal.ofReal_lt_top
  exact ⟨hmass⟩

/-- The root-coordinate measure assigns zero mass outside the topological support of its test. -/
theorem compactTestRootMeasure_compl_tsupport_eq_zero {f : ℂ → ℝ}
    : compactTestRootMeasure f (tsupport f)ᶜ = 0 := by
  rw [compactTestRootMeasure,
    withDensity_apply _ (isClosed_tsupport f).measurableSet.compl,
    ← lintegral_indicator (isClosed_tsupport f).measurableSet.compl]
  calc
    ∫⁻ z, (tsupport f)ᶜ.indicator (fun z => ENNReal.ofReal (f z)) z ∂volume =
        ∫⁻ z, 0 ∂volume := by
      apply lintegral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ (tsupport f)ᶜ
      · simp [hz, image_eq_zero_of_notMem_tsupport (f := f) hz]
      · simp [hz]
    _ = 0 := by simp

/-- A nonnegative test density converts a Bochner integral under its root measure into the
corresponding Lebesgue test integral. -/
theorem integral_compactTestRootMeasure_eq {f g : ℂ → ℝ}
    (hf : Continuous f) (hf_nonneg : ∀ z, 0 ≤ f z) :
    ∫ z, g z ∂compactTestRootMeasure f = ∫ z, f z * g z ∂volume := by
  rw [compactTestRootMeasure, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext z
    rw [smul_eq_mul, ENNReal.toReal_ofReal (hf_nonneg z)]
  · exact measurable_compactTestRootDensity hf
  · exact Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top

end MatedCRTHarmonic.ConeLemmaA10

