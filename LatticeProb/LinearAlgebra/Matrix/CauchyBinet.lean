/-
# Cauchy–Binet over original column subsets

The square minors are indexed by explicit equivalences with the selected subset.
Both minors use the same enumeration, and their product is independent of it.
-/

import LatticeProb.LinearAlgebra.Matrix.RectangularDeterminant
import Mathlib.Data.Fintype.Powerset



namespace Matrix
open scoped BigOperators Classical
noncomputable section
variable {m e R : Type*} [Fintype m] [DecidableEq m] [CommRing R]

/-- Simultaneously re-enumerating the shared subset preserves the product of its
selected column and row determinants. The ambient shared carrier need not be finite. -/
theorem det_submatrix_mul_det_submatrix_eq (A : Matrix m e R) (B : Matrix e m R)
    (S : Finset e) (q q' : m ≃ S) :
    (A.submatrix id (fun i => (q i).val)).det *
        (B.submatrix (fun i => (q i).val) id).det =
      (A.submatrix id (fun i => (q' i).val)).det *
        (B.submatrix (fun i => (q' i).val) id).det := by
  rw [← det_mul, ← det_mul]
  congr 1
  ext i j
  apply Fintype.sum_equiv (q.trans q'.symm)
  intro a
  simp only [submatrix_apply, id_eq, Equiv.trans_apply, Equiv.apply_symm_apply]

private def rowImage (f : {f : m → e // Function.Injective f}) :
    {S : Finset e // S.card = Fintype.card m} :=
  ⟨Finset.univ.image f.val,
    (Finset.card_image_of_injective Finset.univ f.property).trans Finset.card_univ⟩

omit [DecidableEq m] in
private theorem image_univ_enumeration (S : Finset e) (q : m ≃ S) :
    Finset.univ.image (fun i => (q i).val) = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (q i).property
  · intro hx
    exact ⟨q.symm ⟨x, hx⟩, congrArg Subtype.val (q.apply_symm_apply ⟨x, hx⟩)⟩

private def fiberEnumeration (S : {S : Finset e // S.card = Fintype.card m})
    (f : {f : {f : m → e // Function.Injective f} // rowImage f = S}) : m ≃ S.val :=
  Equiv.ofBijective (fun i => ⟨f.val.val i, by
    have h := congrArg Subtype.val f.property
    rw [← h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun _ _ h => f.val.property (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      have h := congrArg Subtype.val f.property
      rw [← h] at hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩

private def rowImageEquiv (S : {S : Finset e // S.card = Fintype.card m})
    (q : m ≃ S.val) : Equiv.Perm m ≃
      {f : {f : m → e // Function.Injective f} // rowImage f = S} where
  toFun σ := ⟨⟨fun i => (q (σ i)).val,
    fun _ _ h => σ.injective (q.injective (Subtype.ext h))⟩,
    Subtype.ext (image_univ_enumeration S.val (σ.trans q))⟩
  invFun f := (fiberEnumeration S f).trans q.symm
  left_inv σ := by
    apply Equiv.ext
    intro i
    change q.symm ⟨(q (σ i)).val, _⟩ = σ i
    exact q.symm_apply_apply (σ i)
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (q (q.symm (fiberEnumeration S f i))).val = f.val.val i
    rw [q.apply_symm_apply]
    rfl

private theorem sum_perm_mul_det_submatrix (C D : Matrix m m R) :
    (∑ σ : Equiv.Perm m, (∏ i : m, C i (σ i)) * (D.submatrix σ id).det) =
      C.det * D.det := by
  calc
    (∑ σ : Equiv.Perm m, (∏ i : m, C i (σ i)) * (D.submatrix σ id).det) =
        (∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i : m, C i (σ i)) *
          D.det := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [det_permute]
      ac_rfl
    _ = C.det * D.det := by
      congr 1
      rw [← det_transpose C, det_apply']
      rfl

/-- **Cauchy–Binet.** Cauchy–Binet for a rectangular product over a commutative ring. The sum
retains every subset of the shared carrier of the required size, and the supplied
equivalences are only indexing data for its paired square minors. -/
theorem det_mul_eq_sum_subsets [Fintype e] (A : Matrix m e R) (B : Matrix e m R)
    (q : ∀ S : {S : Finset e // S.card = Fintype.card m}, m ≃ S.val) :
    (A * B).det =
      ∑ S : {S : Finset e // S.card = Fintype.card m},
        (A.submatrix id (fun i => (q S i).val)).det *
          (B.submatrix (fun i => (q S i).val) id).det := by
  let w : (m → e) → R := fun f => (∏ i : m, A i (f i)) * (B.submatrix f id).det
  calc
    (A * B).det = ∑ f : {f : m → e // Function.Injective f}, w f.val := by
      rw [det_mul_eq_sum_injective]
      exact Finset.sum_subtype _ (fun _ => by simp only [Finset.mem_filter_univ]) w
    _ = ∑ S : {S : Finset e // S.card = Fintype.card m},
        ∑ f : {f : {f : m → e // Function.Injective f} // rowImage f = S},
          w f.val.val :=
      (Fintype.sum_fiberwise rowImage (fun f => w f.val)).symm
    _ = ∑ S : {S : Finset e // S.card = Fintype.card m},
        (A.submatrix id (fun i => (q S i).val)).det *
          (B.submatrix (fun i => (q S i).val) id).det := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← (rowImageEquiv S (q S)).sum_comp (fun f => w f.val.val)]
      change (∑ σ : Equiv.Perm m,
        (∏ i : m, (A.submatrix id (fun i => (q S i).val)) i (σ i)) *
          ((B.submatrix (fun i => (q S i).val) id).submatrix σ id).det) = _
      exact sum_perm_mul_det_submatrix _ _

end
end Matrix
