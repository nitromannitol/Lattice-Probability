module

/-
Integer spans of literal incidence columns on graphs with individual edge copies.
-/

public import LatticeProb.Graph.CopiedGraph.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section



namespace LatticeProb.Graph.CopiedGraph

open scoped Classical BigOperators
noncomputable section
variable {V E : Type*}

/-- The integer coordinate vector at a vertex. -/
def unitColumn (v : V) : V → ℤ := fun x => if x = v then 1 else 0

/-- A root unit column is the coordinate vector supported at that root. -/
theorem unitColumn_eq_single (v : V) : unitColumn v = Pi.single v (1 : ℤ) := by
  ext x
  simp only [unitColumn, Pi.single_apply, eq_comm]

/-- The signed column of an original edge copy, with left endpoint positive. -/
def incidenceColumn (J : CopiedGraph V E) (e : E) : V → ℤ :=
  fun x => (if x = J.left e then 1 else 0) - (if x = J.right e then 1 else 0)

/-- An incidence column is the difference of its two endpoint coordinate vectors. -/
theorem incidenceColumn_eq_sub (J : CopiedGraph V E) (e : E) :
    J.incidenceColumn e = unitColumn (J.left e) - unitColumn (J.right e) := rfl

/-- A copied walk produces an integer linear combination of its available columns. -/
theorem unitColumn_sub_mem_span_of_reaches (J : CopiedGraph V E) (F : Finset E)
    {x y : V} (h : J.reaches F x y) :
    unitColumn x - unitColumn y ∈
      Submodule.span ℤ (Set.range (fun e : F => J.incidenceColumn e.val)) := by
  let S := Submodule.span ℤ (Set.range (fun e : F => J.incidenceColumn e.val))
  induction h with
  | refl => exact sub_self (unitColumn x) ▸ S.zero_mem
  | @tail y z _ hyz ih =>
    obtain ⟨e, he, hends⟩ := hyz
    have hc : J.incidenceColumn e ∈ S := Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
    have hs : unitColumn y - unitColumn z ∈ S := by
      rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [← hl, ← hr]
        exact hc
      · rw [← hr, ← hl, ← neg_sub]
        exact S.neg_mem hc
    simpa only [sub_add_sub_cancel] using S.add_mem ih hs

/-- Original selected edge columns followed by root coordinate columns. -/
def augmentedIncidence (J : CopiedGraph V E) (F : Finset E) (R : Finset V) :
    Matrix V (F ⊕ R) ℤ :=
  fun x c => Sum.elim (fun e : F => J.incidenceColumn e.val x)
    (fun r : R => unitColumn r.val x) c

/-- Root coverage gives all coordinate vectors in the augmented integer column span. -/
theorem unitColumn_mem_span_augmentedIncidence (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) (x : V) :
    unitColumn x ∈ Submodule.span ℤ (Set.range (J.augmentedIncidence F R).col) := by
  obtain ⟨r, hr, hxr⟩ := hcover x
  let S := Submodule.span ℤ (Set.range (J.augmentedIncidence F R).col)
  have hle : Submodule.span ℤ (Set.range (fun e : F => J.incidenceColumn e.val)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl e, rfl⟩
  have hd := hle (J.unitColumn_sub_mem_span_of_reaches F hxr)
  have hu : unitColumn r ∈ S := Submodule.subset_span ⟨Sum.inr ⟨r, hr⟩, rfl⟩
  simpa only [sub_add_cancel] using S.add_mem hd hu

/-- No acyclicity is needed for the augmented columns to span the integer module. -/
theorem span_augmentedIncidence_eq_top [Fintype V] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    Submodule.span ℤ (Set.range (J.augmentedIncidence F R).col) = ⊤ := by
  apply top_unique
  intro f _
  rw [← Finset.univ_sum_single f]
  apply Submodule.sum_mem
  intro x _
  have hx := J.unitColumn_mem_span_augmentedIncidence F R hcover x
  rw [unitColumn_eq_single] at hx
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
    (Submodule.smul_mem _ (f x) hx)

/-- The column-span-to-surjectivity bridge for an arbitrary finite integer matrix. -/
theorem mulVec_surjective_of_span_col_eq_top {A B : Type*} [Fintype B]
    (M : Matrix A B ℤ) (hspan : Submodule.span ℤ (Set.range M.col) = ⊤) :
    Function.Surjective M.mulVec := by
  have hrange : LinearMap.range M.mulVecLin = ⊤ :=
    (Matrix.range_mulVecLin M).trans hspan
  exact LinearMap.range_eq_top.mp hrange

/-- A square integer matrix with spanning columns has unit determinant. -/
theorem isUnit_det_of_span_col_eq_top {A : Type*} [Fintype A] [DecidableEq A]
    (M : Matrix A A ℤ) (hspan : Submodule.span ℤ (Set.range M.col) = ⊤) :
    IsUnit M.det :=
  (Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp
      (mulVec_surjective_of_span_col_eq_top M hspan))

/-- The augmented incidence map is surjective over the integers. -/
theorem mulVec_surjective_augmentedIncidence [Fintype V] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    Function.Surjective (J.augmentedIncidence F R).mulVec :=
  mulVec_surjective_of_span_col_eq_top _ (J.span_augmentedIncidence_eq_top F R hcover)

/-- Any square enumeration of the augmented columns has unit determinant. -/
theorem isUnit_det_augmentedIncidence [Fintype V] [DecidableEq V]
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V) (e : V ≃ F ⊕ R)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    IsUnit ((J.augmentedIncidence F R).submatrix id e).det := by
  apply isUnit_det_of_span_col_eq_top
  have hrange : Set.range ((J.augmentedIncidence F R).submatrix id e).col =
      Set.range (J.augmentedIncidence F R).col := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨e.symm c, ?_⟩
      ext x
      change J.augmentedIncidence F R x (e (e.symm c)) = J.augmentedIncidence F R x c
      rw [Equiv.apply_symm_apply]
  rw [hrange]
  exact J.span_augmentedIncidence_eq_top F R hcover

/-- Enumerate the original selected copies and roots by the vertex carrier when sizes agree. -/
def augmentedEnumeration [Fintype V] (F : Finset E) (R : Finset V)
    (hcard : F.card + R.card = Fintype.card V) : V ≃ F ⊕ R :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    exact hcard.symm)

/-- The square augmented matrix needs only root coverage and the exact size equality. -/
theorem isUnit_det_augmentedIncidence_of_card [Fintype V] [DecidableEq V]
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (hcard : F.card + R.card = Fintype.card V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    IsUnit ((J.augmentedIncidence F R).submatrix id (augmentedEnumeration F R hcard)).det :=
  J.isUnit_det_augmentedIncidence F R (augmentedEnumeration F R hcard) hcover

/-- Delete the root rows and retain every original selected edge copy. -/
def nonrootIncidence (J : CopiedGraph V E) (F : Finset E) (R : Finset V) :
    Matrix {x : V // x ∉ R} F ℤ := fun x e => J.incidenceColumn e.val x.val

/-- Restriction kills the root columns and preserves surjectivity on nonroot coordinates. -/
theorem span_nonrootIncidence_eq_top [Fintype V] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    Submodule.span ℤ (Set.range (J.nonrootIncidence F R).col) = ⊤ := by
  let T := Submodule.span ℤ (Set.range (J.nonrootIncidence F R).col)
  let q : (V → ℤ) →ₗ[ℤ] ({x : V // x ∉ R} → ℤ) :=
    LinearMap.funLeft ℤ ℤ Subtype.val
  have hle : Submodule.span ℤ (Set.range (J.augmentedIncidence F R).col) ≤
      Submodule.comap q T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change q ((J.augmentedIncidence F R).col c) ∈ T
    cases c with
    | inl e => exact Submodule.subset_span ⟨e, rfl⟩
    | inr r =>
      have hz : q ((J.augmentedIncidence F R).col (Sum.inr r)) = 0 := by
        ext x
        change (if x.val = r.val then (1 : ℤ) else 0) = 0
        exact if_neg (fun hx : x.val = r.val => x.property (hx.symm ▸ r.property))
      rw [hz]
      exact T.zero_mem
  rw [J.span_augmentedIncidence_eq_top F R hcover] at hle
  apply top_unique
  intro f _
  let g : V → ℤ := fun x => if h : x ∉ R then f ⟨x, h⟩ else 0
  have hg : q g = f := by
    ext x
    exact dif_pos x.property
  have hmem : q g ∈ T := hle Submodule.mem_top
  exact hg ▸ hmem

/-- The original selected incidence columns surject onto the nonroot integer module. -/
theorem mulVec_surjective_nonrootIncidence [Fintype V] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    Function.Surjective (J.nonrootIncidence F R).mulVec :=
  mulVec_surjective_of_span_col_eq_top _ (J.span_nonrootIncidence_eq_top F R hcover)

/-- Row and column equivalences transport integer surjectivity without additional hypotheses. -/
theorem mulVec_surjective_submatrix_equiv {A B C D : Type*} [Fintype B] [Fintype D]
    (M : Matrix A B ℤ) (a : C ≃ A) (b : D ≃ B)
    (hM : Function.Surjective M.mulVec) :
    Function.Surjective (M.submatrix a b).mulVec := by
  intro v
  obtain ⟨w, hw⟩ := hM (v ∘ a.symm)
  refine ⟨w ∘ b, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  have hb : (w ∘ b) ∘ b.symm = w := by
    ext x
    exact congrArg w (b.apply_symm_apply x)
  rw [hb, hw]
  ext x
  exact congrArg v (a.symm_apply_apply x)

/-- **Unimodularity of a rooted incidence matrix.** Equal-sized enumerations of the nonroot rows and original columns have unit determinant. -/
theorem isUnit_det_nonrootIncidence [Fintype V] {A : Type*} [Fintype A] [DecidableEq A]
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {x : V // x ∉ R}) (b : A ≃ F)
    (hcover : ∀ x, ∃ r ∈ R, J.reaches F x r) :
    IsUnit ((J.nonrootIncidence F R).submatrix a b).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp
    (mulVec_surjective_submatrix_equiv _ a b
      (J.mulVec_surjective_nonrootIncidence F R hcover)))

end
end LatticeProb.Graph.CopiedGraph
