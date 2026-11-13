/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4.Prop210Transfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma31

/-!
# Localized-to-cell-density transfer for [18] Proposition 2.10

Source: [18] (4.19)–(4.20).
The second-moment correction for Proposition 4.8 is: its second-moment argument is
performed without inserting the global event `E^ε` into the conditional expectation. This file only
formalizes the later deterministic implication (4.20): a bound for the localized density `u_*` gives
The corresponding bound for G3's selection-free cell density, with the factor 2 retained explicitly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- The spatial almost-everywhere form of (4.20). The density `uDens` is
selection-free and can sum several cell weights on null cell boundaries, so
this is the form that follows from the paper's selected-cell comparison. -/
theorem prop210Bound_of_localized_integral_ae
    (H : CellularEmbedding G o) {D : Set ℂ} (_hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℂ → ℝ≥0∞) {A η : ℝ}
    (hlocal : ∀ᵐ z ∂volume.restrict D, uDens H z ≤ 2 * uStar z)
    (hbound : (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :
    Prop210Bound H D f (2 * A) (2 * η) := by
  unfold Prop210Bound
  have hpoint : ∀ᵐ z ∂volume.restrict D,
      ENNReal.ofReal (f z) * uDens H z ≤
        2 * (ENNReal.ofReal (f z) * uStar z) := by
    filter_upwards [hlocal] with z hz
    calc
      ENNReal.ofReal (f z) * uDens H z ≤
          ENNReal.ofReal (f z) * (2 * uStar z) :=
        mul_le_mul' le_rfl hz
      _ = 2 * (ENNReal.ofReal (f z) * uStar z) := by ac_rfl
  have hint : (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
      2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
    calc
      _ ≤ ∫⁻ z in D, 2 * (ENNReal.ofReal (f z) * uStar z) :=
        lintegral_mono_ae hpoint
      _ = 2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
        rw [lintegral_const_mul' 2 _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hA : ENNReal.ofReal (2 * A) = ENNReal.ofReal 2 * ENNReal.ofReal A :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  have hη : ENNReal.ofReal (2 * η) = ENNReal.ofReal 2 * ENNReal.ofReal η :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  calc
    (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
        2 * (ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :=
      hint.trans (mul_le_mul' le_rfl hbound)
    _ = ENNReal.ofReal (2 * A) * (∫⁻ z in D, ENNReal.ofReal (f z)) +
        ENNReal.ofReal (2 * η) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num, mul_add, hA, hη]
      ac_rfl

end MatedCRTHarmonic.GMS4

