/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ComplexResolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ComplexifiedOperator
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventRange

/-!
# Positivity and range of the actual complexified full-form resolvent

The complex operator is the proved extension of the existing real 1-resolvent.
Its inner products reduce to real pairings; injectivity reduces to the real and
imaginary parts. Dense range uses mathlib's normal-operator orthogonal-range
identity. No semigroup, process association or extra CFC hypothesis is asserted.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.ComplexSequenceSpace

/-- Complex inner products decompose into the four real pairings of coordinate parts. -/
theorem inner_decomposition {V : Type*} (z w : ComplexL2 V) :
    ⟪z, w⟫_ℂ =
      (⟪realPart V z, realPart V w⟫_ℝ + ⟪imagPart V z, imagPart V w⟫_ℝ : ℂ) +
        Complex.I * (⟪realPart V z, imagPart V w⟫_ℝ -
          ⟪imagPart V z, realPart V w⟫_ℝ : ℂ) := by
  nth_rw 1 [← reconstruction V z]
  nth_rw 1 [← reconstruction V w]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    ofReal_inner]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end ReflectedGMS.ComplexSequenceSpace

namespace ReflectedGMS.FullNetworkForm

open ComplexSequenceSpace

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The actual complex extension of the checked real full-form 1-resolvent. -/
noncomputable def complexOneResolvent (m : V → ℝ) : ComplexL2 V →L[ℂ] ComplexL2 V :=
  complexify (oneResolvent G m)

/-- Embedded real inputs follow exactly the original real resolvent. -/
@[simp] theorem complexOneResolvent_ofReal (m : V → ℝ) (f : ValueSpace V) :
    complexOneResolvent G m (ofReal V f) = ofReal V (oneResolvent G m f) :=
  complexify_ofReal (oneResolvent G m) f

/-- Self-adjointness transports through the exact real/imaginary extension. -/
theorem complexOneResolvent_isSelfAdjoint (m : V → ℝ) :
    IsSelfAdjoint (complexOneResolvent G m) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro z w
  change ⟪complexify (oneResolvent G m) z, w⟫_ℂ =
    ⟪z, complexify (oneResolvent G m) w⟫_ℂ
  rw [inner_decomposition, inner_decomposition]
  simp only [realPart_complexify, imagPart_complexify]
  simp_rw [(oneResolvent_isPositive G m).inner_left_eq_inner_right]

/-- The complex extension is positive on the entire complex Hilbert space. -/
theorem complexOneResolvent_isPositive (m : V → ℝ) :
    (complexOneResolvent G m).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.2
  refine ⟨complexOneResolvent_isSelfAdjoint G m, fun z => ?_⟩
  change 0 ≤ (⟪complexify (oneResolvent G m) z, z⟫_ℂ).re
  rw [inner_decomposition]
  simpa [Complex.mul_re] using
    add_nonneg ((oneResolvent_isPositive G m).inner_nonneg_left (realPart V z))
      ((oneResolvent_isPositive G m).inner_nonneg_left (imagPart V z))

theorem complexOneResolvent_nonneg (m : V → ℝ) : 0 ≤ complexOneResolvent G m :=
  ContinuousLinearMap.nonneg_iff_isPositive.2 (complexOneResolvent_isPositive G m)

/-- Exact norm transport retains the contraction bound. -/
theorem complexOneResolvent_norm_le_one (m : V → ℝ) : ‖complexOneResolvent G m‖ ≤ 1 := by
  simpa only [complexOneResolvent, complexify_norm] using oneResolvent_opNorm_le_one G m

/-- Positive speeds make the complex resolvent injective, by its two real parts. -/
theorem complexOneResolvent_injective (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    Function.Injective (complexOneResolvent G m) := by
  intro z w h
  have hre := congrArg (realPart V) h
  have him := congrArg (imagPart V) h
  apply ext_parts V
  · apply oneResolvent_injective G m hm
    simpa only [complexOneResolvent, realPart_complexify] using hre
  · apply oneResolvent_injective G m hm
    simpa only [complexOneResolvent, imagPart_complexify] using him

theorem complexOneResolvent_ker_eq_bot (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    (complexOneResolvent G m).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (complexOneResolvent_injective G m hm)

/-- The actual complex resolvent has dense range, by self-adjointness and zero kernel. -/
theorem denseRange_complexOneResolvent (m : V → ℝ) (hm : ∀ v, 0 < m v) :
    DenseRange (complexOneResolvent G m) := by
  change Dense ((complexOneResolvent G m).range : Set (ComplexL2 V))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.IsStarNormal.orthogonal_range
      (complexOneResolvent_isSelfAdjoint G m).isStarNormal,
    complexOneResolvent_ker_eq_bot G m hm]

/-- The positive complex operator has real spectrum inside `[0,1]`. -/
theorem complexOneResolvent_spectrum_subset (m : V → ℝ) :
    spectrum ℝ (complexOneResolvent G m) ⊆ Set.Icc (0 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial (ComplexL2 V) with h | h
  · letI := h
    simp only [spectrum.of_subsingleton, Set.empty_subset]
  · letI := h
    intro x hx
    exact ⟨spectrum_nonneg_of_nonneg (complexOneResolvent_nonneg G m) hx,
      (Real.le_norm_self x).trans
        ((spectrum.norm_le_norm_of_mem hx).trans (complexOneResolvent_norm_le_one G m))⟩

end ReflectedGMS.FullNetworkForm
