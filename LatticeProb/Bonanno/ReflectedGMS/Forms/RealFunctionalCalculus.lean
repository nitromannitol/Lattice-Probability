/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.RealFunctionalCalculus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ComplexResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.ComplexifiedOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Real invariance of functional calculus

The actual complexification map has closed real star-algebra image. Mathlib's
`cfc_mem` therefore keeps real-valued continuous functional calculus inside that
image. Its unique real pullback has exactly the same operator norm.

The CFC used here is the existing CFC on complex Hilbert-space operators. No CFC
instance on real Hilbert-space operators or new energy domain is assumed.
-/

-- Merged from `ReflectedGMS/Forms/ComplexificationAlgebra.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ComplexificationAlgebra

/-!
# Real algebra structure of operator complexification

The checked complexification of real sequence-space operators respects the
operator algebra over `ℝ`.  We package that existing map as an isometric real
algebra homomorphism and record that its range is closed.

No adjoint, star-subalgebra, or continuous functional calculus claim is made.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.ComplexSequenceSpace

open FullNetworkForm

variable {V : Type*}

@[simp] theorem complexify_zero :
    complexify (0 : ValueSpace V →L[ℝ] ValueSpace V) =
      (0 : ComplexL2 V →L[ℂ] ComplexL2 V) := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_parts V <;> simp

@[simp] theorem complexify_add
    (S T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexify (S + T) = complexify S + complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_parts V <;> simp

@[simp] theorem complexify_one :
    complexify (1 : ValueSpace V →L[ℝ] ValueSpace V) =
      (1 : ComplexL2 V →L[ℂ] ComplexL2 V) := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_parts V <;> simp

@[simp] theorem complexify_mul
    (S T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexify (S * T) = complexify S * complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_parts V <;> simp

@[simp] theorem complexify_algebraMap (r : ℝ) :
    complexify (algebraMap ℝ (ValueSpace V →L[ℝ] ValueSpace V) r) =
      algebraMap ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) r := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_parts V <;> simp

/-- Complexification as a homomorphism from the real operator algebra into the
complex operator algebra, regarded as an algebra over `ℝ`. -/
noncomputable def complexifyAlgHom :
    (ValueSpace V →L[ℝ] ValueSpace V) →ₐ[ℝ]
      (ComplexL2 V →L[ℂ] ComplexL2 V) where
  toFun := complexify
  map_zero' := complexify_zero
  map_add' := complexify_add
  map_one' := complexify_one
  map_mul' := complexify_mul
  commutes' := complexify_algebraMap

@[simp] theorem complexifyAlgHom_apply
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexifyAlgHom T = complexify T := rfl

/-- The real algebra embedding is isometric for the operator norm. -/
theorem complexifyAlgHom_isometry : Isometry (complexifyAlgHom (V := V)) :=
  (AddMonoidHomClass.isometry_iff_norm (complexifyAlgHom (V := V))).2 complexify_norm

/-- The real operator algebra has closed image in the complex operator algebra. -/
theorem isClosed_range_complexifyAlgHom :
    IsClosed (Set.range (complexifyAlgHom (V := V))) :=
  complexifyAlgHom_isometry.isClosedEmbedding.isClosed_range

end ReflectedGMS.ComplexSequenceSpace

end Merged_ComplexificationAlgebra

-- Merged from `ReflectedGMS/Forms/ComplexAdjoint.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ComplexAdjoint

/-! The complex extension preserves the existing Hilbert adjoint. The proof
uses only the checked real-pairing decomposition and mathlib's adjoint identity. -/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.ComplexSequenceSpace

open FullNetworkForm

/-- Complexification commutes with the Hilbert adjoint for every bounded real operator. -/
theorem complexify_adjoint {V : Type*} (T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexify T.adjoint = (complexify T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro z w
  rw [inner_decomposition, inner_decomposition]
  simp only [realPart_complexify, imagPart_complexify]
  simp_rw [T.adjoint_inner_left]

/-- The exact star-preservation identity needed for the real star-algebra embedding. -/
@[simp] theorem complexify_star {V : Type*} (T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexify (star T) = star (complexify T) :=
  complexify_adjoint T

end ReflectedGMS.ComplexSequenceSpace

end Merged_ComplexAdjoint

set_option autoImplicit false

namespace ReflectedGMS.ComplexSequenceSpace

open FullNetworkForm

variable {V : Type*}

/-- Select the existing restriction of the complex operator algebra. Its real
scalar action agrees pointwise with the sequence-space action; specifying the
action avoids the two separate instance paths through `lp` and through `ℂ`. -/
noncomputable local instance : SMul ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  ⟨fun r T => (r : ℂ) • T⟩
noncomputable local instance : Algebra ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  Algebra.complexToReal
local instance : StarModule ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) where
  star_smul r T := by
    change star ((r : ℂ) • T) = (r : ℂ) • star T
    rw [star_smul]
    simp

/-- The checked algebra embedding also preserves the Hilbert adjoint. -/
noncomputable def complexifyStarAlgHom :
    (ValueSpace V →L[ℝ] ValueSpace V) →⋆ₐ[ℝ]
      (ComplexL2 V →L[ℂ] ComplexL2 V) where
  toFun := complexify
  map_zero' := complexify_zero
  map_add' := complexify_add
  map_one' := complexify_one
  map_mul' := complexify_mul
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro z
    change complexify (algebraMap ℝ (ValueSpace V →L[ℝ] ValueSpace V) r) z = (r : ℂ) • z
    apply ext_parts V
    · rw [realPart_complexify, realPart_complex_smul]
      simp
    · rw [imagPart_complexify, imagPart_complex_smul]
      simp
  map_star' := complexify_star

@[simp] theorem complexifyStarAlgHom_apply
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexifyStarAlgHom T = complexify T := rfl

/-- The real operator image, with its actual inherited star-algebra structure. -/
noncomputable def realOperatorImage :
    StarSubalgebra ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  (complexifyStarAlgHom (V := V)).range

theorem isClosed_realOperatorImage :
    IsClosed (realOperatorImage (V := V) : Set (ComplexL2 V →L[ℂ] ComplexL2 V)) :=
  isClosed_range_complexifyAlgHom

/-- Real operators are star-algebra equivalent to their complexified image. -/
noncomputable def complexifyEquivRange :
    (ValueSpace V →L[ℝ] ValueSpace V) ≃⋆ₐ[ℝ] realOperatorImage (V := V) :=
  StarAlgEquiv.ofInjective complexifyStarAlgHom complexifyAlgHom_isometry.injective

/-- Every real-valued CFC remains in the real operator image. As usual, CFC is
totalized to zero when its continuity or self-adjointness condition fails. -/
theorem cfc_complexify_mem (f : ℝ → ℝ)
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    cfc f (complexify T) ∈ realOperatorImage (V := V) := by
  have hle : StarAlgebra.elemental ℝ (complexify T) ≤ realOperatorImage (V := V) :=
    StarSubalgebra.topologicalClosure_minimal
      (StarAlgebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨T, rfl⟩))
      isClosed_realOperatorImage
  exact hle (cfc_mem_elemental f (complexify T))

/-- The real operator obtained by pulling the existing complex CFC back along
the exact star-algebra equivalence onto the closed real image. -/
noncomputable def realCFC (f : ℝ → ℝ)
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    ValueSpace V →L[ℝ] ValueSpace V :=
  complexifyEquivRange.symm ⟨cfc f (complexify T), cfc_complexify_mem f T⟩

@[simp] theorem complexify_realCFC (f : ℝ → ℝ)
    (T : ValueSpace V →L[ℝ] ValueSpace V) :
    complexify (realCFC f T) = cfc f (complexify T) := by
  exact congrArg Subtype.val
    (complexifyEquivRange.apply_symm_apply
      ⟨cfc f (complexify T), cfc_complexify_mem f T⟩)

end ReflectedGMS.ComplexSequenceSpace
