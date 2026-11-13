/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ComplexSequenceSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Real and complex square-summable sequences

The coordinate maps are instances of the existing `lp.mapCLM` lift. Their
summability, linearity and continuity are supplied by mathlib. The only new
proofs here identify the lifted maps, reconstruction and the exact Hilbert norm.
The existing real energy domain and resolvent are unchanged.
-/

set_option autoImplicit false

open scoped ENNReal

namespace ReflectedGMS.ComplexSequenceSpace

open FullNetworkForm

/-- The existing complex `lp 2` space on the same vertex index type. -/
noncomputable abbrev ComplexL2 (V : Type*) := lp (fun _ : V => ℂ) 2

variable (V : Type*)

/-- Coordinatewise real part, lifted by the existing uniformly bounded-map API. -/
noncomputable def realPart : ComplexL2 V →L[ℝ] ValueSpace V :=
  lp.mapCLM 2 (fun _ : V => Complex.reCLM) zero_le_one
    (fun _ => Complex.reCLM_norm.le)

/-- Coordinatewise imaginary part, with its existing real-linear structure. -/
noncomputable def imagPart : ComplexL2 V →L[ℝ] ValueSpace V :=
  lp.mapCLM 2 (fun _ : V => Complex.imCLM) zero_le_one
    (fun _ => Complex.imCLM_norm.le)

/-- Coordinatewise real embedding into complex square-summable sequences. -/
noncomputable def ofReal : ValueSpace V →L[ℝ] ComplexL2 V :=
  lp.mapCLM 2 (fun _ : V => Complex.ofRealCLM) zero_le_one
    (fun _ => Complex.ofRealCLM_norm.le)

@[simp] theorem realPart_apply (z : ComplexL2 V) (v : V) :
    realPart V z v = (z v).re := rfl

@[simp] theorem imagPart_apply (z : ComplexL2 V) (v : V) :
    imagPart V z v = (z v).im := rfl

@[simp] theorem ofReal_apply (f : ValueSpace V) (v : V) :
    ofReal V f v = (f v : ℂ) := rfl

@[simp] theorem realPart_ofReal (f : ValueSpace V) : realPart V (ofReal V f) = f := by
  apply lp.ext
  funext v
  simp

@[simp] theorem imagPart_ofReal (f : ValueSpace V) : imagPart V (ofReal V f) = 0 := by
  apply lp.ext
  funext v
  simp

/-- Every complex square-summable sequence reconstructs from its real parts. -/
theorem reconstruction (z : ComplexL2 V) :
    ofReal V (realPart V z) + Complex.I • ofReal V (imagPart V z) = z := by
  apply lp.ext
  funext v
  change ((z v).re : ℂ) + Complex.I * ((z v).im : ℂ) = z v
  simpa only [mul_comm Complex.I] using Complex.re_add_im (z v)

/-- Equality of the real and imaginary parts determines the entire sequence. -/
theorem ext_parts {z w : ComplexL2 V}
    (hre : realPart V z = realPart V w) (him : imagPart V z = imagPart V w) : z = w := by
  rw [← reconstruction V z, ← reconstruction V w, hre, him]

/-- The real embedding is injective. -/
theorem ofReal_injective : Function.Injective (ofReal V) := by
  intro f g h
  simpa only [realPart_ofReal] using congrArg (realPart V) h

/-- The real embedding preserves the actual `lp 2` norm. -/
@[simp] theorem ofReal_norm (f : ValueSpace V) : ‖ofReal V f‖ = ‖f‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro v
    simp only [ofReal_apply, Complex.norm_real, le_refl]
  · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro v
    simp only [ofReal_apply, Complex.norm_real, le_refl]

private theorem norm_sq_eq_tsum {E : V → Type*} [∀ v, NormedAddCommGroup (E v)]
    (z : lp E 2) : ‖z‖ ^ 2 = ∑' v, ‖z v‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (E := E) (p := 2) (by norm_num) z)

/-- The exact real/imaginary decomposition of the complex Hilbert norm. -/
theorem norm_sq_decomposition (z : ComplexL2 V) :
    ‖z‖ ^ 2 = ‖realPart V z‖ ^ 2 + ‖imagPart V z‖ ^ 2 := by
  have hs (f : ValueSpace V) : Summable (fun v => ‖f v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum, norm_sq_eq_tsum,
    ← (hs (realPart V z)).tsum_add (hs (imagPart V z))]
  apply tsum_congr
  intro v
  simp only [realPart_apply, imagPart_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply]
  ring

end ReflectedGMS.ComplexSequenceSpace
