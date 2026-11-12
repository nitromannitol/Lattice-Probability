/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.Lateral at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Symm
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea7
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# The lateral part of a whole-plane GFF paired with a test function

For a whole-plane GFF `X` and a test function `φ`, almost surely

  `⟨X − X_{|·|}(0), φ⟩ = ⟨X, φ − φ̄⟩` (`ae_lateralPartC_apply`, `ae_lateralPart_apply`)

where `φ̄` is the rotation average of `φ` (`symmTest`). This identifies the lateral part of the field (DMS Def 4.10; DMS Lemmas 4.2–4.4) as a *linear* functional of `X`: the radial profile paired with `φ` equals the radial
profile paired with `φ̄` (`integral_symmTest_mul`, the profile being radial), and that is `⟨X, φ̄⟩` because the lateral
part kills radial test functions (ported MoT `ConeArea7.ae_lateralPartC_radial`, from LQGMetric's DFGPS radial
pairing formula). Local integrability of the radial profile: ported MoT `ConeArea4.ae_radial_R2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric MatedCRTHarmonic.MoTPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- The radial profile `z ↦ h_{|z|}(0)` is rotation invariant. -/
lemma isRotInv_radialFun (h : DistC) : IsRotInv (radialFun h) := by
  intro α w
  simp only [radialFun, norm_mul, norm_exp_ofReal_mul_I', one_mul]

/-- The symmetrization of a test function is a radial test function in MoT's sense. -/
lemma isRadialTest_symmTest (φ : TestC) : ConeArea7.IsRadialTest (symmTest φ) :=
  symmTest_radial φ

/-- **The lateral pairing** (MoT's `lateralPartC`): a.s. `⟨lateralPartC X, φ⟩ = ⟨X, φ − φ̄⟩`. -/
theorem ae_lateralPartC_apply (hX : IsWholePlaneGFF X P) (φ : TestC) :
    ∀ᵐ ω ∂P, lateralPartC (X ω) φ = X ω (φ - symmTest φ) := by
  have := hX.gaussian.isProbabilityMeasure
  filter_upwards [ConeArea7.ae_lateralPartC_radial hX (isRadialTest_symmTest φ),
    ConeArea4.ae_radial_R2 hX] with ω h0 h3
  obtain ⟨R, -, -, hRe, hRl⟩ := h3
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  rw [lateralPartC_apply hloc] at h0 ⊢
  rw [← integral_symmTest_mul φ (isRotInv_radialFun (X ω)) hloc, map_sub]
  linarith

/-- **The lateral pairing** (`CellScaling.lateralPart`): a.s. `⟨lateralPart X, φ⟩ = ⟨X, φ − φ̄⟩`. -/
theorem ae_lateralPart_apply (hX : IsWholePlaneGFF X P) (φ : TestC) :
    ∀ᵐ ω ∂P, CellScaling.lateralPart (X ω) φ = X ω (φ - symmTest φ) :=
  ae_lateralPartC_apply hX φ

end MatedCRTHarmonic.GMCFacts
