/-
# Ordered row insertion and determinant signs

Moving a newly inserted row from its sorted position to the first position
contributes exactly the finite-subset insertion sign.
-/

import LatticeProb.LinearAlgebra.FiniteSubsetContraction
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Interval.Finset.Fin



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical
noncomputable section

/-- Deleting the position of an inserted element from the increasing enumeration
recovers the original increasing enumeration. -/
theorem orderEmb_insert_succAbove {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (i : Fin n) (hi : i ∉ S) :
    let hT : (insert i S).card = k + 1 := (Finset.card_insert_of_notMem hi).trans
      (congrArg Nat.succ hS)
    let p := ((insert i S).orderIsoOfFin hT).symm ⟨i, Finset.mem_insert_self i S⟩
    (fun j => (insert i S).orderEmbOfFin hT (p.succAbove j)) = S.orderEmbOfFin hS := by
  dsimp only
  let hT : (insert i S).card = k + 1 := (Finset.card_insert_of_notMem hi).trans
    (congrArg Nat.succ hS)
  let q := (insert i S).orderIsoOfFin hT
  let p := q.symm ⟨i, Finset.mem_insert_self i S⟩
  have hpi : (insert i S).orderEmbOfFin hT p = i :=
    congrArg Subtype.val (q.apply_symm_apply ⟨i, Finset.mem_insert_self i S⟩)
  apply Finset.orderEmbOfFin_unique hS
  · intro j
    have hj := (insert i S).orderEmbOfFin_mem hT (p.succAbove j)
    rcases Finset.mem_insert.mp hj with he | he
    · exact False.elim ((Fin.succAbove_ne p j)
        (((insert i S).orderEmbOfFin hT).injective (he.trans hpi.symm)))
    · exact he
  · exact ((insert i S).orderEmbOfFin hT).strictMono.comp (Fin.strictMono_succAbove p)

/-- The sorted position of a newly inserted element counts precisely the old
subset elements below it. -/
theorem insertion_position_eq_card_filter {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (i : Fin n) (hi : i ∉ S) :
    let hT : (insert i S).card = k + 1 := (Finset.card_insert_of_notMem hi).trans
      (congrArg Nat.succ hS)
    let p := ((insert i S).orderIsoOfFin hT).symm ⟨i, Finset.mem_insert_self i S⟩
    (p : ℕ) = (S.filter (fun j => j < i)).card := by
  dsimp only
  let hT : (insert i S).card = k + 1 := (Finset.card_insert_of_notMem hi).trans
    (congrArg Nat.succ hS)
  let q := (insert i S).orderIsoOfFin hT
  let p := q.symm ⟨i, Finset.mem_insert_self i S⟩
  have hpi : (insert i S).orderEmbOfFin hT p = i :=
    congrArg Subtype.val (q.apply_symm_apply ⟨i, Finset.mem_insert_self i S⟩)
  have himage : (Finset.Iio p).image ((insert i S).orderEmbOfFin hT) =
      S.filter (fun j => j < i) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hji : (insert i S).orderEmbOfFin hT j < i := by
        exact (((insert i S).orderEmbOfFin hT).strictMono
          (Finset.mem_Iio.mp hj)).trans_eq hpi
      have hmem := (insert i S).orderEmbOfFin_mem hT j
      exact Finset.mem_filter.mpr ⟨(Finset.mem_insert.mp hmem).resolve_left hji.ne, hji⟩
    · intro hx
      obtain ⟨hxS, hxi⟩ := Finset.mem_filter.mp hx
      let j := q.symm ⟨x, Finset.mem_insert_of_mem hxS⟩
      have hjx : (insert i S).orderEmbOfFin hT j = x :=
        congrArg Subtype.val (q.apply_symm_apply ⟨x, Finset.mem_insert_of_mem hxS⟩)
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr ?_, hjx⟩
      apply ((insert i S).orderEmbOfFin hT).lt_iff_lt.mp
      rw [hjx, hpi]
      exact hxi
  rw [← himage, Finset.card_image_of_injective _
    ((insert i S).orderEmbOfFin hT).injective, Fin.card_Iio]

/-- **Ordered minor insertion sign.** Inserting a row in first position rather than sorted position contributes
exactly the CAR coefficient insertion sign. -/
theorem det_cons_rows_eq_insertionSign {n k : ℕ}
    (U : Matrix (Fin n) (Fin (k + 1)) ℝ) (S : Finset (Fin n))
    (hS : S.card = k) (i : Fin n) (hi : i ∉ S) :
    (U.submatrix (Fin.cons i (S.orderEmbOfFin hS)) id).det =
      insertionSign S i * determinantCoeff U (insert i S) := by
  let hT : (insert i S).card = k + 1 := (Finset.card_insert_of_notMem hi).trans
    (congrArg Nat.succ hS)
  let q := (insert i S).orderIsoOfFin hT
  let p := q.symm ⟨i, Finset.mem_insert_self i S⟩
  have hpi : (insert i S).orderEmbOfFin hT p = i :=
    congrArg Subtype.val (q.apply_symm_apply ⟨i, Finset.mem_insert_self i S⟩)
  have henum : ((insert i S).orderEmbOfFin hT : Fin (k + 1) → Fin n) =
      p.insertNth i (S.orderEmbOfFin hS) :=
    Fin.eq_insertNth_iff.mpr ⟨hpi, orderEmb_insert_succAbove S hS i hi⟩
  have hm : U.submatrix (Fin.cons i (S.orderEmbOfFin hS)) id =
      (U.submatrix ((insert i S).orderEmbOfFin hT) id).submatrix p.cycleRange.symm id := by
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, henum, Fin.insertNth_apply_cycleRange_symm]
  rw [hm, Matrix.det_permute, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  rw [determinantCoeff_of_card_eq U (insert i S) hT,
    insertionSign_eq_pow_card_filter]
  have hc : (p : ℕ) = (S.filter (fun j => j < i)).card :=
    insertion_position_eq_card_filter S hS i hi
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow,
    Int.cast_neg, Int.cast_one, hc]

end
end LatticeProb.SubsetContraction
