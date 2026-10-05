import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeClassLayer

/-!
# Image classes under a linear map (Raic, Lemma 2.3, with the correction D-b)

Packet P12 of the staged formalisation of Raic's Theorem 1.3 (A multivariate Berry-Esseen theorem
with explicit constants, arXiv:1802.06475), item L3 of the feasibility report.

For a regular class `C : MvbeRegularClass m κ` (Raic's (A1)-(A8)) and an invertible linear map
`T` of `ℝ^m = EuclideanSpace ℝ (Fin m)` (a continuous linear equivalence), the *image class*
`MvbeRegularClass.imageCLE C T : MvbeRegularClass m κ` has

* sets `{T A : A ∈ C.cls}`, and
* signed distances `ρ̃_B(x) = ρ_{T⁻¹ B}(T⁻¹ x) / c`, `c := ‖T⁻¹‖` (operator norm).

Raic's Lemma 2.3 assumes that the smallest singular value of `T` is at least one, so that `T⁻¹`
is non-expansive and no normalisation is needed.  For a general `T` the division by `c = ‖T⁻¹‖`
(and by nothing else) makes `ρ̃` non-expansive for every `T`, and the constant of (A8) stays
exactly `κ`: with `U = T⁻¹`,
`∇ρ̃_B(x) = c⁻¹ Uᵀ ∇ρ(U x)`, `‖Uᵀ‖ = c`, `min (ρ̃(x), ρ̃(y)) = min (ρ(Ux), ρ(Uy)) / c`, hence
`‖∇ρ̃(x) - ∇ρ̃(y)‖ ≤ κ ‖U (x - y)‖ / min ρ ≤ κ c ‖x - y‖ / min ρ = κ ‖x - y‖ / min ρ̃`
(`mvbeImage_a8_gradient_sub_le`).  All of (A1)-(A7) and measurability are proved in the
`mvbeImage_*` lemmas, then assembled in `MvbeRegularClass.imageCLE`.  `[NeZero m]` is needed for
`c > 0`.

The matrix version is `MvbeRegularClass.image C L hL` for an invertible real matrix `L`
(`hL : IsUnit L.det`; a positive definite `L` has this by `mvbe_isUnit_det_of_posDef`), where `L`
acts on `EuclideanSpace ℝ (Fin m)` through `Matrix.toEuclideanCLM`, with inverse
`Matrix.toEuclideanCLM L⁻¹` (`mvbeMatrixCLE`).  Symmetry of `L` is not needed.

**Perimeter bound** (`MvbeRegularClass.image_gammaStar_le`), for `γ = stdGaussian`,
`c = ‖L⁻¹‖`, `σ = min 1 (1/‖L‖)`:
`γ*(L C | ρ̃) ≤ γ*(C | ρ) · (c / σ)`, i.e. the constant is `max (1, ‖L‖) ‖L⁻¹‖`
(`MvbeRegularClass.image_gammaStar_le_max`).  Route: `γ(L S) = N(0, L⁻¹ L⁻ᵀ)(S)` (the push-forward
of `stdGaussian` under a matrix `M` is `multivariateGaussian 0 (M Mᵀ)`,
`mvbe_stdGaussian_map_toEuclideanCLM`, by uniqueness of the characteristic function), the lower
bound `L⁻¹ L⁻ᵀ ⪰ σ² 1` (`mvbe_quadForm_lower`) and the Gaussian layer estimate of Raic's Lemma 2.2
(`mvbe_gaussian_layer_diff_le_of_quadForm`, `mvbe_gaussian_diff_layer_le_of_quadForm`), applied to
the layers `(T A)^{ε|ρ̃} = T (A^{cε|ρ})` (`mvbe_layer_image`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder Pointwise

namespace LatticeProb

section ImageClass

variable {m : ℕ} {κ : ℝ}

/-- The dilation constant `c = ‖T⁻¹‖` (operator norm of the inverse) of the image class. -/
noncomputable def mvbeInvNorm
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  ‖(T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖

theorem mvbeInvNorm_pos [NeZero m]
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) : 0 < mvbeInvNorm T :=
  T.norm_symm_pos

theorem mvbe_norm_symm_le
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) : ‖T.symm x‖ ≤ mvbeInvNorm T * ‖x‖ :=
  (T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)).le_opNorm x

/-- The class of images `T '' A`, `A ∈ C.cls`. -/
def mvbeImageCls (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {B | ∃ A ∈ C.cls, B = T '' A}

/-- The signed distances of the image class: `ρ̃_B(x) = ρ_{T⁻¹ B}(T⁻¹ x) / ‖T⁻¹‖`. -/
noncomputable def mvbeImageRho (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : Set (EuclideanSpace ℝ (Fin m))) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  C.rho (T.symm '' B) (T.symm x) / mvbeInvNorm T

theorem mvbe_mem_imageCls_iff (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : Set (EuclideanSpace ℝ (Fin m))) : B ∈ mvbeImageCls C T ↔ T.symm '' B ∈ C.cls := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    rwa [T.symm_image_image]
  · intro h
    exact ⟨_, h, (T.image_symm_image B).symm⟩

@[simp]
theorem mvbeImageRho_image (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (x : EuclideanSpace ℝ (Fin m)) :
    mvbeImageRho C T (T '' A) x = C.rho A (T.symm x) / mvbeInvNorm T := by
  simp [mvbeImageRho]

theorem mvbe_layer_image [NeZero m] (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (t : ℝ) :
    mvbeLayer (mvbeImageRho C T) (T '' A) t = T '' mvbeLayer C.rho A (mvbeInvNorm T * t) := by
  ext x
  rw [T.image_eq_preimage_symm (mvbeLayer C.rho A _), Set.mem_preimage]
  simp only [mvbeLayer, Set.mem_setOf_eq, mvbeImageRho_image]
  rw [div_le_iff₀ (mvbeInvNorm_pos T), mul_comm t]

theorem mvbe_symm_image_translate
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (y : EuclideanSpace ℝ (Fin m)) :
    T.symm '' ((fun x => x + y) '' (T '' A)) = (fun x => x + T.symm y) '' A := by
  simp only [Set.image_image, map_add, ContinuousLinearEquiv.symm_apply_apply]

theorem mvbe_image_translate
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (y : EuclideanSpace ℝ (Fin m)) :
    (fun x => x + y) '' (T '' A) = T '' ((fun x => x + T.symm y) '' A) := by
  rw [← mvbe_symm_image_translate T A y, T.image_symm_image]

theorem mvbe_symm_image_scale
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (q : ℝ) :
    T.symm '' ((fun x => q • x) '' (T '' A)) = (fun x => q • x) '' A := by
  simp only [Set.image_image, map_smul, ContinuousLinearEquiv.symm_apply_apply]

theorem mvbe_image_scale
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanSpace ℝ (Fin m))) (q : ℝ) :
    (fun x => q • x) '' (T '' A) = T '' ((fun x => q • x) '' A) := by
  rw [← mvbe_symm_image_scale T A q, T.image_symm_image]

/-! ### Gradient of a composition with a linear equivalence -/

theorem mvbe_hasGradientAt_comp_equiv_div {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin m)}
    (U : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) (c : ℝ)
    {x : EuclideanSpace ℝ (Fin m)} (h : HasGradientAt f g (U x)) :
    HasGradientAt (fun z => f (U z) / c)
      (c⁻¹ • ContinuousLinearMap.adjoint
        (U : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) g) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have h2 : HasFDerivAt (fun z => c⁻¹ • f (U z))
      (c⁻¹ • ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m)) g).comp
        (U : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))) x :=
    (h.comp x U.hasFDerivAt).const_smul c⁻¹
  have e1 : (fun z => f (U z) / c) = fun z => c⁻¹ • f (U z) := by
    funext z
    rw [smul_eq_mul, div_eq_inv_mul]
  rw [e1]
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

/-! ### The fields of the image class -/

section Fields

variable (C : MvbeRegularClass m κ)
  (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))

theorem mvbeImage_measurableSet_mem : ∀ B ∈ mvbeImageCls C T, MeasurableSet B := by
  rintro _ ⟨A, hA, rfl⟩
  rw [T.image_eq_preimage_symm]
  exact T.symm.continuous.measurable (C.measurableSet_mem A hA)

theorem mvbeImage_measurable_rho :
    ∀ B ∈ mvbeImageCls C T, Measurable (mvbeImageRho C T B) := by
  rintro _ ⟨A, hA, rfl⟩
  have : mvbeImageRho C T (T '' A) = fun x => C.rho A (T.symm x) / mvbeInvNorm T :=
    funext (mvbeImageRho_image C T A)
  rw [this]
  exact ((C.measurable_rho A hA).comp T.symm.continuous.measurable).div_const _

theorem mvbeImage_a1_translate : ∀ B ∈ mvbeImageCls C T, ∀ y : EuclideanSpace ℝ (Fin m),
    (fun x => x + y) '' B ∈ mvbeImageCls C T := by
  rintro _ ⟨A, hA, rfl⟩ y
  exact ⟨_, C.a1_translate A hA (T.symm y), mvbe_image_translate T A y⟩

theorem mvbeImage_a1_scale : ∀ B ∈ mvbeImageCls C T, ∀ q : ℝ, 1 < q →
    (fun x => q • x) '' B ∈ mvbeImageCls C T := by
  rintro _ ⟨A, hA, rfl⟩ q hq
  exact ⟨_, C.a1_scale A hA q hq, mvbe_image_scale T A q⟩

theorem mvbeImage_a2 [NeZero m] : ∀ B ∈ mvbeImageCls C T, ∀ t : ℝ,
    mvbeLayer (mvbeImageRho C T) B t ∈ mvbeImageCls C T ∪ {∅, Set.univ} := by
  rintro _ ⟨A, hA, rfl⟩ t
  rw [mvbe_layer_image]
  rcases C.a2 A hA (mvbeInvNorm T * t) with h | h
  · exact Or.inl ⟨_, h, rfl⟩
  · rcases h with h | h
    · right
      simp [h]
    · right
      simp [Set.mem_singleton_iff.1 h, Set.image_univ_of_surjective T.surjective]

theorem mvbeImage_a3 [NeZero m] : ∀ B ∈ mvbeImageCls C T, ∀ ε : ℝ, 0 < ε →
    mvbeLayer (mvbeImageRho C T) B (-ε) = ∅ ∨
      {x | mvbeImageRho C T (mvbeLayer (mvbeImageRho C T) B (-ε)) x < ε} ⊆ B := by
  rintro _ ⟨A, hA, rfl⟩ ε hε
  have hc := mvbeInvNorm_pos T
  rw [mvbe_layer_image, mul_neg]
  rcases C.a3 A hA (mvbeInvNorm T * ε) (mul_pos hc hε) with h | h
  · left
    rw [h, Set.image_empty]
  · right
    intro x hx
    simp only [Set.mem_setOf_eq, mvbeImageRho_image] at hx
    rw [div_lt_iff₀ hc, mul_comm ε] at hx
    exact ⟨T.symm x, h hx, T.apply_symm_apply x⟩

theorem mvbeImage_a4_nonpos [NeZero m] :
    ∀ B ∈ mvbeImageCls C T, ∀ x ∈ B, mvbeImageRho C T B x ≤ 0 := by
  rintro _ ⟨A, hA, rfl⟩ x ⟨a, ha, rfl⟩
  rw [mvbeImageRho_image, T.symm_apply_apply]
  exact div_nonpos_of_nonpos_of_nonneg (C.a4_nonpos A hA a ha) (mvbeInvNorm_pos T).le

theorem mvbeImage_a4_nonneg [NeZero m] :
    ∀ B ∈ mvbeImageCls C T, ∀ x ∉ B, 0 ≤ mvbeImageRho C T B x := by
  rintro _ ⟨A, hA, rfl⟩ x hx
  rw [mvbeImageRho_image]
  refine div_nonneg (C.a4_nonneg A hA _ ?_) (mvbeInvNorm_pos T).le
  intro h
  exact hx ⟨_, h, T.apply_symm_apply x⟩

theorem mvbeImage_a5 : ∀ B ∈ mvbeImageCls C T, ∀ y x : EuclideanSpace ℝ (Fin m),
    mvbeImageRho C T ((fun z => z + y) '' B) (x + y) = mvbeImageRho C T B x := by
  rintro _ ⟨A, hA, rfl⟩ y x
  rw [mvbe_image_translate T A y, mvbeImageRho_image, mvbeImageRho_image, map_add,
    C.a5 A hA (T.symm y) (T.symm x)]

theorem mvbeImage_a6 [NeZero m] : ∀ B ∈ mvbeImageCls C T, ∀ q : ℝ, 1 ≤ q →
    ∀ x : EuclideanSpace ℝ (Fin m),
    |mvbeImageRho C T ((fun z => q • z) '' B) (q • x)| ≤ q * |mvbeImageRho C T B x| := by
  rintro _ ⟨A, hA, rfl⟩ q hq x
  have hc := mvbeInvNorm_pos T
  rw [mvbe_image_scale T A q, mvbeImageRho_image, mvbeImageRho_image, map_smul, abs_div,
    abs_div, abs_of_pos hc, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (C.a6 A hA q hq (T.symm x)) hc.le

theorem mvbeImage_a7 [NeZero m] : ∀ B ∈ mvbeImageCls C T, ∀ x y : EuclideanSpace ℝ (Fin m),
    0 ≤ mvbeImageRho C T B x → 0 ≤ mvbeImageRho C T B y →
    |mvbeImageRho C T B x - mvbeImageRho C T B y| ≤ ‖x - y‖ := by
  rintro _ ⟨A, hA, rfl⟩ x y hx hy
  have hc := mvbeInvNorm_pos T
  rw [mvbeImageRho_image] at hx hy ⊢
  rw [mvbeImageRho_image]
  have hx' : 0 ≤ C.rho A (T.symm x) := by
    have := mul_nonneg hx hc.le
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  have hy' : 0 ≤ C.rho A (T.symm y) := by
    have := mul_nonneg hy hc.le
    rwa [div_mul_cancel₀ _ hc.ne'] at this
  have h7 := C.a7 A hA _ _ hx' hy'
  rw [← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |C.rho A (T.symm x) - C.rho A (T.symm y)| ≤ ‖T.symm x - T.symm y‖ := h7
    _ = ‖T.symm (x - y)‖ := by rw [map_sub]
    _ ≤ mvbeInvNorm T * ‖x - y‖ := mvbe_norm_symm_le T _
    _ = ‖x - y‖ * mvbeInvNorm T := mul_comm _ _

theorem mvbeImage_pos_of_pos [NeZero m] {A : Set (EuclideanSpace ℝ (Fin m))}
    {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < mvbeImageRho C T (T '' A) x) :
    0 < C.rho A (T.symm x) := by
  rw [mvbeImageRho_image] at hx
  have := mul_pos hx (mvbeInvNorm_pos T)
  rwa [div_mul_cancel₀ _ (mvbeInvNorm_pos T).ne'] at this

theorem mvbeImage_hasGradientAt [NeZero m] {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls)
    {x : EuclideanSpace ℝ (Fin m)} (hx : 0 < C.rho A (T.symm x)) :
    HasGradientAt (mvbeImageRho C T (T '' A))
      ((mvbeInvNorm T)⁻¹ • ContinuousLinearMap.adjoint
        (T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
          (gradient (C.rho A) (T.symm x))) x := by
  have : mvbeImageRho C T (T '' A) = fun z => C.rho A (T.symm z) / mvbeInvNorm T :=
    funext (mvbeImageRho_image C T A)
  rw [this]
  exact mvbe_hasGradientAt_comp_equiv_div T.symm _
    (C.a8_differentiableAt A hA _ hx).hasGradientAt

theorem mvbeImage_a8_differentiableAt [NeZero m] :
    ∀ B ∈ mvbeImageCls C T, ∀ x : EuclideanSpace ℝ (Fin m), 0 < mvbeImageRho C T B x →
      DifferentiableAt ℝ (mvbeImageRho C T B) x := by
  rintro _ ⟨A, hA, rfl⟩ x hx
  exact (mvbeImage_hasGradientAt C T hA (mvbeImage_pos_of_pos C T hx)).differentiableAt

theorem mvbeImage_a8_gradient_sub_le [NeZero m] :
    ∀ B ∈ mvbeImageCls C T, ∀ x y : EuclideanSpace ℝ (Fin m),
      0 < mvbeImageRho C T B x → 0 < mvbeImageRho C T B y →
      ‖gradient (mvbeImageRho C T B) x - gradient (mvbeImageRho C T B) y‖
        ≤ κ * ‖x - y‖ / min (mvbeImageRho C T B x) (mvbeImageRho C T B y) := by
  rintro _ ⟨A, hA, rfl⟩ x y hx hy
  have hc := mvbeInvNorm_pos T
  have hx' := mvbeImage_pos_of_pos C T hx
  have hy' := mvbeImage_pos_of_pos C T hy
  rw [(mvbeImage_hasGradientAt C T hA hx').gradient, (mvbeImage_hasGradientAt C T hA hy').gradient,
    mvbeImageRho_image, mvbeImageRho_image, min_div_div_right hc.le, div_div_eq_mul_div]
  have h8 := C.a8_gradient_sub_le A hA (T.symm x) (T.symm y) hx' hy'
  have hm0 : 0 < min (C.rho A (T.symm x)) (C.rho A (T.symm y)) := lt_min hx' hy'
  set c := mvbeInvNorm T with hcdef
  set a := gradient (C.rho A) (T.symm x)
  set b := gradient (C.rho A) (T.symm y)
  set U := (T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) with hU'
  have hadj : ‖ContinuousLinearMap.adjoint U‖ = c := by
    rw [LinearIsometryEquiv.norm_map]
    rfl
  have hU : ‖ContinuousLinearMap.adjoint U (a - b)‖ ≤ c * ‖a - b‖ := by
    have := (ContinuousLinearMap.adjoint U).le_opNorm (a - b)
    rwa [hadj] at this
  calc ‖c⁻¹ • ContinuousLinearMap.adjoint U a - c⁻¹ • ContinuousLinearMap.adjoint U b‖
      = c⁻¹ * ‖ContinuousLinearMap.adjoint U (a - b)‖ := by
        rw [← smul_sub, ← map_sub, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc]
    _ ≤ c⁻¹ * (c * ‖a - b‖) := by gcongr
    _ = ‖a - b‖ := by field_simp
    _ ≤ κ * ‖T.symm x - T.symm y‖ / min (C.rho A (T.symm x)) (C.rho A (T.symm y)) := h8
    _ ≤ κ * ‖x - y‖ * c / min (C.rho A (T.symm x)) (C.rho A (T.symm y)) := by
        refine div_le_div_of_nonneg_right ?_ hm0.le
        have h1 : ‖T.symm x - T.symm y‖ ≤ c * ‖x - y‖ := by
          rw [← map_sub]
          exact mvbe_norm_symm_le T _
        have h2 := mul_le_mul_of_nonneg_left h1 C.kappa_nonneg
        linarith


end Fields

/-- **The image class** (Raic, Lemma 2.3, with the normalisation `‖T⁻¹‖` of the feasibility
report, item D-b).  For a regular class `C` and a continuous linear equivalence `T` of `ℝ^m`,
the class `{T A : A ∈ C}` with `ρ̃_B(x) = ρ_{T⁻¹ B}(T⁻¹ x) / ‖T⁻¹‖` satisfies (A1)-(A8) with the
SAME `κ`.  The factor `1/‖T⁻¹‖` makes `ρ̃` non-expansive for every `T` (no assumption on the
singular values of `T` is needed), and it is what keeps `κ` unchanged in (A8): with
`c = ‖T⁻¹‖`, `∇ρ̃_B(x) = c⁻¹ (T⁻¹)ᵀ ∇ρ(T⁻¹ x)`, `‖(T⁻¹)ᵀ‖ = c`, and `min ρ̃ = (min ρ) / c`,
so that `‖∇ρ̃(x) - ∇ρ̃(y)‖ ≤ κ ‖T⁻¹(x - y)‖ / min ρ ≤ κ c ‖x - y‖ / min ρ = κ ‖x - y‖ / min ρ̃`. -/
noncomputable def MvbeRegularClass.imageCLE [NeZero m] (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) : MvbeRegularClass m κ where
  cls := mvbeImageCls C T
  rho := mvbeImageRho C T
  kappa_nonneg := C.kappa_nonneg
  measurableSet_mem := mvbeImage_measurableSet_mem C T
  measurable_rho := mvbeImage_measurable_rho C T
  a1_translate := mvbeImage_a1_translate C T
  a1_scale := mvbeImage_a1_scale C T
  a2 := mvbeImage_a2 C T
  a3 := mvbeImage_a3 C T
  a4_nonpos := mvbeImage_a4_nonpos C T
  a4_nonneg := mvbeImage_a4_nonneg C T
  a5 := mvbeImage_a5 C T
  a6 := mvbeImage_a6 C T
  a7 := mvbeImage_a7 C T
  a8_differentiableAt := mvbeImage_a8_differentiableAt C T
  a8_gradient_sub_le := mvbeImage_a8_gradient_sub_le C T

end ImageClass

section GaussPush

/-! ### Push-forward of the standard Gaussian under a matrix -/

variable {m : ℕ}

theorem mvbe_charFun_map_clm (μ : Measure (EuclideanSpace ℝ (Fin m)))
    (U : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (t : EuclideanSpace ℝ (Fin m)) :
    charFun (μ.map U) t = charFun μ (ContinuousLinearMap.adjoint U t) := by
  rw [charFun_apply, charFun_apply, integral_map U.continuous.measurable.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem mvbe_adjoint_toEuclideanCLM (M : Matrix (Fin m) (Fin m) ℝ) :
    ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) M) = toEuclideanCLM (𝕜 := ℝ) Mᵀ := by
  have h := map_star (toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) M
  rw [ContinuousLinearMap.star_eq_adjoint] at h
  rw [← h]
  simp [Matrix.star_eq_conjTranspose]

theorem mvbe_dotProduct_mul_transpose (M : Matrix (Fin m) (Fin m) ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    t ⬝ᵥ (M * Mᵀ) *ᵥ t = ‖ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) M) t‖ ^ 2 := by
  rw [← inner_toEuclideanCLM, map_mul, ← mvbe_adjoint_toEuclideanCLM,
    mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

theorem mvbe_stdGaussian_map_toEuclideanCLM (M : Matrix (Fin m) (Fin m) ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map (toEuclideanCLM (𝕜 := ℝ) M)
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (M * Mᵀ) := by
  have hS : (M * Mᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose M
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [mvbe_charFun_map_clm, charFun_stdGaussian, charFun_multivariateGaussian hS,
    mvbe_dotProduct_mul_transpose]
  simp [neg_div]

end GaussPush

section Perimeter

/-! ### The perimeter bound -/

variable {m : ℕ}

/-- If `A` is a left inverse of `T`, then `‖t‖ ≤ ‖T‖ ‖A† t‖` (`A†` the adjoint of `A`). -/
theorem mvbe_norm_le_adjoint
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : ∀ x, A (T x) = x) (t : EuclideanSpace ℝ (Fin m)) :
    ‖t‖ ≤ ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖
      * ‖ContinuousLinearMap.adjoint A t‖ := by
  rcases eq_or_lt_of_le (norm_nonneg t) with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have h1 : ‖t‖ * ‖t‖ ≤ ‖t‖ * (‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖
        * ‖ContinuousLinearMap.adjoint A t‖) := by
      have e : inner ℝ (ContinuousLinearMap.adjoint A t) (T t) = ‖t‖ * ‖t‖ := by
        rw [ContinuousLinearMap.adjoint_inner_left, hA, real_inner_self_eq_norm_mul_norm]
      have h2 := real_inner_le_norm (ContinuousLinearMap.adjoint A t) (T t)
      have h3 : ‖T t‖ ≤ ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖ * ‖t‖ :=
        (T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)).le_opNorm t
      rw [e] at h2
      calc ‖t‖ * ‖t‖ ≤ ‖ContinuousLinearMap.adjoint A t‖ * ‖T t‖ := h2
        _ ≤ ‖ContinuousLinearMap.adjoint A t‖
            * (‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖ * ‖t‖) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1 hpos

end Perimeter



section PerimeterBound

variable {m : ℕ} [NeZero m] {κ : ℝ}

/-- Quadratic-form lower bound for the covariance `M Mᵀ` of `T⁻¹_# γ`: with `σ = min 1 (1/‖T‖)`,
`σ² ‖v‖² ≤ ⟪M Mᵀ v, v⟫` whenever the matrix `M` represents `T⁻¹`. -/
theorem mvbe_quadForm_lower
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : toEuclideanCLM (𝕜 := ℝ) M
      = (T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (v : EuclideanSpace ℝ (Fin m)) :
    (min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖)) ^ 2 * ‖v‖ ^ 2
      ≤ inner ℝ (WithLp.toLp 2 ((M * Mᵀ) *ᵥ WithLp.ofLp v)) v := by
  have hT : 0 < ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖ := T.norm_pos
  rw [mvbe_inner_toLp_mulVec, mvbe_dotProduct_mul_transpose]
  have hA : ∀ x, toEuclideanCLM (𝕜 := ℝ) M (T x) = x := by
    intro x
    rw [hM]
    exact T.symm_apply_apply x
  have h1 := mvbe_norm_le_adjoint T (toEuclideanCLM (𝕜 := ℝ) M) hA v
  have h2 : min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖) * ‖v‖
      ≤ ‖ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) M) v‖ := by
    calc _ ≤ (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ ≤ (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖)
            * (‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖
              * ‖ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℝ) M) v‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp
  calc _ = (min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖)
        * ‖v‖) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (le_min zero_le_one (by positivity)) (norm_nonneg _))
        h2 2

/-- **Perimeter of the image class.**  For a regular class `C` and a continuous linear equivalence
`T`, with `c = ‖T⁻¹‖` and `σ = min 1 (1/‖T‖)`,
`γ*(T C | ρ̃) ≤ γ*(C | ρ) · c / σ` for the standard Gaussian `γ`. -/
theorem MvbeRegularClass.imageCLE_gammaStar_le (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (C.imageCLE T).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
        * ENNReal.ofReal (mvbeInvNorm T
          / min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖)) := by
  have hT : 0 < ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖ := T.norm_pos
  have hc := mvbeInvNorm_pos T
  have hσ : 0 < min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖) :=
    lt_min one_pos (by positivity)
  have hσ1 : min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖) ≤ 1 :=
    min_le_left _ _
  generalize hσdef : min 1 (1 / ‖(T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖)
    = σ at hσ hσ1 ⊢
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin m) (Fin m) ℝ, toEuclideanCLM (𝕜 := ℝ) M
      = (T.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    ⟨(toEuclideanCLM (𝕜 := ℝ)).symm _, (toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _⟩
  have hpush : (stdGaussian (EuclideanSpace ℝ (Fin m))).map T.symm
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (M * Mᵀ) := by
    have := mvbe_stdGaussian_map_toEuclideanCLM M
    rw [hM] at this
    exact this
  have hsymm : (M * Mᵀ).IsSymm := Matrix.isSymm_mul_transpose_self M
  have hlow := mvbe_quadForm_lower T M hM
  rw [hσdef] at hlow
  have hmeas : ∀ S : Set (EuclideanSpace ℝ (Fin m)), MeasurableSet S →
      stdGaussian (EuclideanSpace ℝ (Fin m)) (T '' S)
        = multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (M * Mᵀ) S := by
    intro S hS
    rw [← hpush, Measure.map_apply T.symm.continuous.measurable hS, T.image_eq_preimage_symm]
  unfold MvbeRegularClass.gammaStar mvbeGammaStar
  refine iSup₂_le fun B hB => ?_
  obtain ⟨A, hA, rfl⟩ := hB
  unfold mvbeGammaStarOf
  refine iSup₂_le fun ε hε => ?_
  have hcε : 0 < mvbeInvNorm T * ε := mul_pos hc hε
  have hrw : ENNReal.ofReal (mvbeInvNorm T * ε / σ)
      = ENNReal.ofReal ε * ENNReal.ofReal (mvbeInvNorm T / σ) := by
    rw [← ENNReal.ofReal_mul hε.le]
    congr 1
    ring
  rw [ENNReal.div_le_iff' (by simpa using hε) ENNReal.ofReal_ne_top]
  refine max_le ?_ ?_
  · have key : mvbeLayer (C.imageCLE T).rho (T '' A) ε
        = T '' mvbeLayer C.rho A (mvbeInvNorm T * ε) := mvbe_layer_image C T A ε
    rw [key, ← Set.image_sdiff T.injective, hmeas _ (mvbe_measurableSet_layer_diff C hA _)]
    refine (mvbe_gaussian_layer_diff_le_of_quadForm C hA hcε 0 hσ hσ1 hsymm hlow).trans ?_
    rw [hrw, mul_left_comm]
    exact le_rfl
  · have key : mvbeLayer (C.imageCLE T).rho (T '' A) (-ε)
        = T '' mvbeLayer C.rho A (-(mvbeInvNorm T * ε)) := by
      rw [← mul_neg]
      exact mvbe_layer_image C T A (-ε)
    rw [key, ← Set.image_sdiff T.injective, hmeas _ (mvbe_measurableSet_diff_layer C hA _)]
    refine (mvbe_gaussian_diff_layer_le_of_quadForm C hA hcε 0 hσ hσ1 hsymm hlow).trans ?_
    rw [hrw, mul_left_comm]
    exact le_rfl

end PerimeterBound


section MatrixImage

variable {m : ℕ} {κ : ℝ}

/-- A positive definite real matrix is invertible: `IsUnit L.det`. -/
theorem mvbe_isUnit_det_of_posDef {L : Matrix (Fin m) (Fin m) ℝ} (hL : L.PosDef) :
    IsUnit L.det :=
  (Matrix.isUnit_iff_isUnit_det L).1 hL.isUnit

/-- The continuous linear equivalence of `ℝ^m = EuclideanSpace ℝ (Fin m)` induced by an
invertible real matrix `L` (acting through `Matrix.toEuclideanCLM`, i.e. `x ↦ L *ᵥ x`); its
inverse is `Matrix.toEuclideanCLM L⁻¹`. -/
noncomputable def mvbeMatrixCLE (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearEquiv.equivOfInverse' (toEuclideanCLM (𝕜 := ℝ) L)
    (toEuclideanCLM (𝕜 := ℝ) L⁻¹)
    (by
      have := congrArg (toEuclideanCLM (𝕜 := ℝ)) (Matrix.mul_nonsing_inv L hL)
      rwa [map_mul, map_one] at this)
    (by
      have := congrArg (toEuclideanCLM (𝕜 := ℝ)) (Matrix.nonsing_inv_mul L hL)
      rwa [map_mul, map_one] at this)

theorem mvbeMatrixCLE_apply (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det)
    (x : EuclideanSpace ℝ (Fin m)) : mvbeMatrixCLE L hL x = toEuclideanCLM (𝕜 := ℝ) L x :=
  rfl

theorem mvbeMatrixCLE_symm_apply (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det)
    (x : EuclideanSpace ℝ (Fin m)) :
    (mvbeMatrixCLE L hL).symm x = toEuclideanCLM (𝕜 := ℝ) L⁻¹ x :=
  rfl

theorem mvbeInvNorm_matrixCLE (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    mvbeInvNorm (mvbeMatrixCLE L hL) = ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖ :=
  rfl

theorem mvbe_norm_matrixCLE (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    ‖(mvbeMatrixCLE L hL : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖
      = ‖toEuclideanCLM (𝕜 := ℝ) L‖ :=
  rfl

/-- **The image class `L C`** of a regular class `C` under an invertible matrix `L`
(Raic, Lemma 2.3, with the normalisation of the feasibility report, item D-b; `L` acts on
`EuclideanSpace ℝ (Fin m)` through `Matrix.toEuclideanCLM`).  Its sets are `L A`, `A ∈ C`, and
`ρ̃_B(x) = ρ_{L⁻¹ B}(L⁻¹ x) / ‖L⁻¹‖` (see `MvbeRegularClass.image_cls`,
`MvbeRegularClass.image_rho`).  It is a regular class with the same `κ`.  For `L` symmetric
positive definite use `mvbe_isUnit_det_of_posDef` to produce `hL`. -/
noncomputable def MvbeRegularClass.image [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) : MvbeRegularClass m κ :=
  C.imageCLE (mvbeMatrixCLE L hL)

theorem MvbeRegularClass.image_cls [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    (C.image L hL).cls = {B | ∃ A ∈ C.cls, B = toEuclideanCLM (𝕜 := ℝ) L '' A} :=
  rfl

theorem MvbeRegularClass.image_rho [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) (B : Set (EuclideanSpace ℝ (Fin m)))
    (x : EuclideanSpace ℝ (Fin m)) :
    (C.image L hL).rho B x
      = C.rho (toEuclideanCLM (𝕜 := ℝ) L⁻¹ '' B) (toEuclideanCLM (𝕜 := ℝ) L⁻¹ x)
        / ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖ :=
  rfl

/-- `‖L⁻¹‖ > 0` for an invertible matrix `L` (as `m ≥ 1`). -/
theorem mvbe_norm_inv_pos [NeZero m] (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    0 < ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖ :=
  mvbeInvNorm_pos (mvbeMatrixCLE L hL)

/-- **Perimeter of the image class under a matrix.**  With `c = ‖L⁻¹‖` and
`σ = min 1 (1/‖L‖)` (operator norms),
`γ*(L C | ρ̃) ≤ γ*(C | ρ) · (c / σ)` for the standard Gaussian `γ`. -/
theorem MvbeRegularClass.image_gammaStar_le [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    (C.image L hL).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
        * ENNReal.ofReal (‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖
          / min 1 (1 / ‖toEuclideanCLM (𝕜 := ℝ) L‖)) :=
  C.imageCLE_gammaStar_le (mvbeMatrixCLE L hL)

/-- `c / min 1 (1/a) = max 1 a * c` for `a > 0`: the constant of the perimeter bound is
`max (1, ‖L‖) ‖L⁻¹‖`, as in the feasibility report (item D-b). -/
theorem mvbe_div_min_one_div {a c : ℝ} (ha : 0 < a) :
    c / min 1 (1 / a) = max 1 a * c := by
  rcases le_total 1 a with h | h
  · have h1 : 1 / a ≤ 1 := (div_le_one ha).2 h
    rw [min_eq_right h1, max_eq_right h]
    field_simp
  · rw [min_eq_left ((one_le_div ha).2 h), max_eq_left h]
    ring

theorem MvbeRegularClass.image_gammaStar_le_max [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) :
    (C.image L hL).gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m)))
        * ENNReal.ofReal (max 1 ‖toEuclideanCLM (𝕜 := ℝ) L‖
          * ‖toEuclideanCLM (𝕜 := ℝ) L⁻¹‖) := by
  have hpos : 0 < ‖toEuclideanCLM (𝕜 := ℝ) L‖ := (mvbeMatrixCLE L hL).norm_pos
  have := C.image_gammaStar_le L hL
  rwa [mvbe_div_min_one_div hpos] at this

end MatrixImage

end LatticeProb
