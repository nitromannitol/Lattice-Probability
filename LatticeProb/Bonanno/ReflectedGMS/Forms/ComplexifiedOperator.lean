/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ComplexifiedOperator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ComplexSequenceSpace

/-!
# The bounded complex extension of a real sequence operator

The same real-linear map assembled from the existing real/imaginary adapters is
proved complex-linear and re-bundled. Its exact bound follows from the checked
Hilbert norm decomposition. No real energy domain or resolvent is changed.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.ComplexSequenceSpace

open FullNetworkForm

variable {V : Type*}

/-- Real part of complex scalar multiplication, in the existing sequence spaces. -/
theorem realPart_complex_smul (c : ℂ) (z : ComplexL2 V) :
    realPart V (c • z) = c.re • realPart V z - c.im • imagPart V z := by
  apply lp.ext
  funext v
  change (c * z v).re = c.re * (z v).re - c.im * (z v).im
  exact Complex.mul_re c (z v)

/-- Imaginary part of complex scalar multiplication. -/
theorem imagPart_complex_smul (c : ℂ) (z : ComplexL2 V) :
    imagPart V (c • z) = c.re • imagPart V z + c.im • realPart V z := by
  apply lp.ext
  funext v
  change (c * z v).im = c.re * (z v).im + c.im * (z v).re
  exact Complex.mul_im c (z v)

/-- Assemble the extension using only composition, addition and scalar multiplication
of the already checked real continuous linear maps. -/
noncomputable def complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ComplexL2 V →L[ℝ] ComplexL2 V :=
  (ofReal V).comp (T.comp (realPart V)) +
    Complex.I • ((ofReal V).comp (T.comp (imagPart V)))

@[simp] theorem complexifyReal_apply (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) (v : V) :
    complexifyReal T z v = (T (realPart V z) v : ℂ) +
      Complex.I * (T (imagPart V z) v : ℂ) := rfl

@[simp] theorem realPart_complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : realPart V (complexifyReal T z) = T (realPart V z) := by
  apply lp.ext
  funext v
  simp [realPart_apply, complexifyReal_apply, Complex.mul_re]

@[simp] theorem imagPart_complexifyReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : imagPart V (complexifyReal T z) = T (imagPart V z) := by
  apply lp.ext
  funext v
  simp [imagPart_apply, complexifyReal_apply, Complex.mul_im]

/-- The extension is a genuine continuous complex-linear operator. -/
noncomputable def complexify (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ComplexL2 V →L[ℂ] ComplexL2 V where
  __ := complexifyReal T
  map_smul' c z := by
    change complexifyReal T (c • z) = c • complexifyReal T z
    apply ext_parts V
    · simp only [realPart_complexifyReal, realPart_complex_smul, map_sub, map_smul,
        imagPart_complexifyReal]
    · simp only [imagPart_complexifyReal, imagPart_complex_smul, map_add, map_smul,
        realPart_complexifyReal]

@[simp] theorem realPart_complexify (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : realPart V (complexify T z) = T (realPart V z) :=
  realPart_complexifyReal T z

@[simp] theorem imagPart_complexify (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : imagPart V (complexify T z) = T (imagPart V z) :=
  imagPart_complexifyReal T z

/-- The extension agrees exactly with the original real operator. -/
@[simp] theorem complexify_ofReal (T : ValueSpace V →L[ℝ] ValueSpace V)
    (f : ValueSpace V) : complexify T (ofReal V f) = ofReal V (T f) := by
  apply ext_parts V <;> simp

/-- The original operator norm controls the complex extension on every vector. -/
theorem complexify_apply_norm_le (T : ValueSpace V →L[ℝ] ValueSpace V)
    (z : ComplexL2 V) : ‖complexify T z‖ ≤ ‖T‖ * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg (complexify T z))
    (mul_nonneg (norm_nonneg T) (norm_nonneg z))).1
  rw [norm_sq_decomposition V (complexify T z), realPart_complexify,
    imagPart_complexify, mul_pow, norm_sq_decomposition V z]
  have hre := (sq_le_sq₀ (norm_nonneg (T (realPart V z)))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (realPart V z)))).2
      (T.le_opNorm (realPart V z))
  have him := (sq_le_sq₀ (norm_nonneg (T (imagPart V z)))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (imagPart V z)))).2
      (T.le_opNorm (imagPart V z))
  calc
    _ ≤ (‖T‖ * ‖realPart V z‖) ^ 2 + (‖T‖ * ‖imagPart V z‖) ^ 2 :=
      add_le_add hre him
    _ = _ := by ring

/-- The complex extension has no larger operator norm. -/
theorem complexify_norm_le (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ‖complexify T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) (complexify_apply_norm_le T)

/-- The isometric real embedding gives the reverse inequality as well. -/
@[simp] theorem complexify_norm (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ‖complexify T‖ = ‖T‖ := by
  apply le_antisymm (complexify_norm_le T)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (complexify T))
  intro f
  simpa only [complexify_ofReal, ofReal_norm] using
    (complexify T).le_opNorm (ofReal V f)

/-- The exact inner-product bridge for embedded real vectors. This is the
minimal adapter needed for subsequent self-adjointness/positivity transport. -/
theorem ofReal_inner (f g : ValueSpace V) :
    ⟪ofReal V f, ofReal V g⟫_ℂ = (⟪f, g⟫_ℝ : ℂ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.ofReal_tsum]
  apply tsum_congr
  intro v
  simp [ofReal_apply, RCLike.inner_apply]

end ReflectedGMS.ComplexSequenceSpace
