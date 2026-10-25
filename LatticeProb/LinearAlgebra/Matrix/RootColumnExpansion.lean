module

/-
Determinant expansion along increasingly ordered final unit columns.
-/

public import LatticeProb.Data.Finset.SuccAbove
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section



namespace Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- A final unit column deletes its supporting row with the usual zero-based cofactor sign. -/
theorem det_eq_neg_one_pow_mul_det_submatrix_of_last_column {t : ℕ}
    (C : Matrix (Fin (t + 1)) (Fin (t + 1)) R) (r : Fin (t + 1))
    (h : ∀ x, C x (Fin.last t) = if x = r then 1 else 0) :
    C.det = (-1 : R) ^ ((r : ℕ) + t) *
      (C.submatrix r.succAbove Fin.castSucc).det := by
  rw [det_succ_column C (Fin.last t)]
  rw [Finset.sum_eq_single r]
  · rw [h, if_pos rfl, mul_one]
    rw [Fin.succAbove_last, Fin.val_last]
  · intro x _ hxr
    rw [h, if_neg hxr, mul_zero, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ r))

/-- Ordered final unit columns leave the increasing complementary row minor,
with the sum of root labels and final column positions as cofactor exponent. -/
theorem det_eq_neg_one_pow_mul_det_submatrix_of_last_columns {d k : ℕ}
    (C : Matrix (Fin (d + k)) (Fin (d + k)) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k)
    (hunit : ∀ (x : Fin (d + k)) (r : Fin k),
      C x (Fin.natAdd d r) = if x = I.orderEmbOfFin hI r then 1 else 0) :
    C.det =
      (-1 : R) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ r : Fin k, (d + (r : ℕ)))) *
        (C.submatrix
          (Iᶜ.orderEmbOfFin
            (show Iᶜ.card = d by
              rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]))
          (Fin.castAdd k)).det := by
  induction k with
  | zero =>
    have hIe : I = ∅ := Finset.card_eq_zero.mp hI
    have hrow : Iᶜ.orderEmbOfFin
        (show Iᶜ.card = d by
          rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]) =
        (OrderIso.refl (Fin d)).toOrderEmbedding := by
      symm
      apply Finset.orderEmbOfFin_unique'
      intro a
      simp only [hIe, Finset.compl_empty, Finset.mem_univ]
    rw [hrow, hIe]
    simp only [Finset.sum_empty, Finset.univ_eq_empty, add_zero,
      pow_zero, one_mul]
    rfl
  | succ k ih =>
    let r := I.orderEmbOfFin hI (Fin.last k)
    let J := I.preimageSuccAbove r
    have hr : r ∈ I := Finset.orderEmbOfFin_mem I hI (Fin.last k)
    have hJ : J.card = k := by
      rw [Finset.card_preimageSuccAbove I r hr, hI, Nat.add_sub_cancel]
    have hJc : Jᶜ.card = d := by
      rw [Finset.card_compl, Fintype.card_fin, hJ]
      exact Nat.add_sub_cancel d k
    have hIc : Iᶜ.card = d := by
      rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]
    let D := C.submatrix r.succAbove Fin.castSucc
    have hsmall : ∀ (x : Fin (d + k)) (j : Fin k),
        D x (Fin.natAdd d j) = if x = J.orderEmbOfFin hJ j then 1 else 0 := by
      intro x j
      change C (r.succAbove x) (Fin.castSucc (Fin.natAdd d j)) = _
      rw [Fin.castSucc_natAdd, hunit]
      rw [← Finset.orderEmbOfFin_preimageSuccAbove I hI r rfl hJ j]
      simp only [Fin.succAbove_right_inj]
      rfl
    have hminor : D.submatrix (Jᶜ.orderEmbOfFin hJc) (Fin.castAdd k) =
        C.submatrix (Iᶜ.orderEmbOfFin hIc) (Fin.castAdd (k + 1)) := by
      ext a b
      change C (r.succAbove (Jᶜ.orderEmbOfFin hJc a))
        (Fin.castSucc (Fin.castAdd k b)) = _
      rw [Finset.orderEmbOfFin_preimageSuccAbove_compl I r hIc hJc,
        Fin.castSucc_castAdd]
      rfl
    have hlast : ∀ x, C x (Fin.last (d + k)) = if x = r then 1 else 0 := by
      intro x
      exact hunit x (Fin.last k)
    have hmax : ∀ x ∈ I, x ≤ r := by
      intro x hx
      have hxrange : x ∈ Set.range (I.orderEmbOfFin hI) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hxrange
      exact (I.orderEmbOfFin hI).monotone j.le_last
    have hsum := Finset.sum_val_preimageSuccAbove I r hr hmax
    rw [det_eq_neg_one_pow_mul_det_submatrix_of_last_column C r hlast,
      ih D J hJ hsmall, hminor, ← mul_assoc, ← pow_add]
    have hpositions : (∑ j : Fin (k + 1), (d + (j : ℕ))) =
        (∑ j : Fin k, (d + (j : ℕ))) + (d + k) := by
      rw [Fin.sum_univ_castSucc]
      rfl
    have hexp : (r : ℕ) + (d + k) +
        ((∑ x ∈ J, (x : ℕ)) + (∑ j : Fin k, (d + (j : ℕ)))) =
        (∑ x ∈ I, (x : ℕ)) + (∑ j : Fin (k + 1), (d + (j : ℕ))) := by
      calc
        _ = ((∑ x ∈ J, (x : ℕ)) + (r : ℕ)) +
            ((∑ j : Fin k, (d + (j : ℕ))) + (d + k)) := by ac_rfl
        _ = _ := congrArg₂ Nat.add hsum.symm hpositions.symm
    exact congrArg (fun t => (-1 : R) ^ t *
      (C.submatrix (Iᶜ.orderEmbOfFin hIc) (Fin.castAdd (k + 1))).det) hexp

/-- Append increasingly ordered root unit columns to a rectangular matrix. -/
def appendRootColumns {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k) :
    Matrix (Fin (d + k)) (Fin (d + k)) R :=
  fun x j => Fin.addCases (A x)
    (fun r => if x = I.orderEmbOfFin hI r then 1 else 0) j

/-- The initial columns of the appended matrix are the original columns. -/
@[simp]
theorem appendRootColumns_castAdd {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k) (x : Fin (d + k)) (a : Fin d) :
    appendRootColumns A I hI x (Fin.castAdd k a) = A x a :=
  Fin.addCases_left a

/-- The final columns of the appended matrix are exactly the specified unit vectors. -/
@[simp]
theorem appendRootColumns_natAdd {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k) (x : Fin (d + k)) (r : Fin k) :
    appendRootColumns A I hI x (Fin.natAdd d r) =
      if x = I.orderEmbOfFin hI r then 1 else 0 :=
  Fin.addCases_right r

/-- **Expansion along root columns.** Appending ordered root columns realizes the signed deleted-row minor. -/
theorem det_appendRootColumns {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k) :
    (appendRootColumns A I hI).det =
      (-1 : R) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ r : Fin k, (d + (r : ℕ)))) *
        (A.submatrix
          (Iᶜ.orderEmbOfFin
            (show Iᶜ.card = d by
              rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel]))
          id).det := by
  rw [det_eq_neg_one_pow_mul_det_submatrix_of_last_columns _ I hI
    (appendRootColumns_natAdd A I hI)]
  congr 1
  congr 1
  ext a b
  exact appendRootColumns_castAdd A I hI _ b

end Matrix
