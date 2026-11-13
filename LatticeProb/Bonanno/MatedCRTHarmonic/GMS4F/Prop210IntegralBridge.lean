/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.Prop210IntegralBridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410Rooting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import Mathlib.Probability.Independence.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop210
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Real and lower integrals for Proposition 2.10

Proposition 4.10 uses finite real integrals. Proposition 2.10's graph event
uses lower Lebesgue integrals. The conversion is valid for nonnegative,
integrable products; these conditions are needed when applying (4.20).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4F

/-- The form needed for a Proposition 2.10 test: nonnegativity is required
only on its integration domain. -/
theorem setLIntegral_ofReal_mul_eq_of_integrableOn
    (D : Set ℂ) (hD : MeasurableSet D) (f g : ℂ → ℝ)
    (hf : ∀ z ∈ D, 0 ≤ f z) (hg : ∀ z ∈ D, 0 ≤ g z)
    (hInt : IntegrableOn (fun z => f z * g z) D) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (g z)) =
      ENNReal.ofReal (∫ z in D, f z * g z) := by
  have hnn : ∀ᵐ z ∂volume.restrict D, 0 ≤ f z * g z :=
    (ae_restrict_iff' hD).2
      (Filter.Eventually.of_forall fun z hz => mul_nonneg (hf z hz) (hg z hz))
  rw [ofReal_integral_eq_lintegral_ofReal hInt hnn]
  apply lintegral_congr_ae
  exact (ae_restrict_iff' hD).2
    (Filter.Eventually.of_forall fun z hz => (ENNReal.ofReal_mul (hf z hz)).symm)

/-- A finite real integral bound transfers to the lower-integral inequality
used by Proposition 2.10. -/
theorem lintegral_bound_of_real_integral_bound
    (D : Set ℂ) (hD : MeasurableSet D) (f g : ℂ → ℝ)
    (hf : ∀ z ∈ D, 0 ≤ f z) (hg : ∀ z ∈ D, 0 ≤ g z)
    (hInt : IntegrableOn (fun z => f z * g z) D)
    (hIntf : IntegrableOn f D)
    {A threshold eta : ℝ} (hA : 0 ≤ A)
    (hthreshold : 0 ≤ threshold) (heta : threshold ≤ eta)
    (hbound : (∫ z in D, f z * g z) ≤
      A * (∫ z in D, f z) + threshold) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (g z)) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) +
        ENNReal.ofReal eta := by
  have hfnn : ∀ᵐ z ∂volume.restrict D, 0 ≤ f z :=
    (ae_restrict_iff' hD).2 (Filter.Eventually.of_forall hf)
  have hIf : 0 ≤ ∫ z in D, f z := integral_nonneg_of_ae hfnn
  have hEta0 : 0 ≤ eta := hthreshold.trans heta
  have hIfEq : (∫⁻ z in D, ENNReal.ofReal (f z)) =
      ENNReal.ofReal (∫ z in D, f z) :=
    (ofReal_integral_eq_lintegral_ofReal hIntf hfnn).symm
  rw [setLIntegral_ofReal_mul_eq_of_integrableOn D hD f g hf hg hInt, hIfEq]
  calc
    ENNReal.ofReal (∫ z in D, f z * g z) ≤
        ENNReal.ofReal (A * (∫ z in D, f z) + threshold) :=
      ENNReal.ofReal_le_ofReal hbound
    _ ≤ ENNReal.ofReal (A * (∫ z in D, f z) + eta) :=
      ENNReal.ofReal_le_ofReal (add_le_add_right heta _)
    _ = ENNReal.ofReal A * ENNReal.ofReal (∫ z in D, f z) +
          ENNReal.ofReal eta := by
      rw [ENNReal.ofReal_add (mul_nonneg hA hIf) hEta0, ENNReal.ofReal_mul hA]

end MatedCRTHarmonic.GMS4F

