module

/-
Paired ordered incidence minors retain the exact component root permutation sign.
-/

public import LatticeProb.Graph.CopiedGraph.RootMatching
public import LatticeProb.Graph.CopiedGraph.IncidenceSpan
public import LatticeProb.LinearAlgebra.Matrix.ColumnSpanDeterminant
public import Mathlib.Tactic.Ring

@[expose] public section



namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section

/-- An actual ordered root matching supplies rootedness at the second root set. -/
theorem IsRootedForest.of_ordered_matching {V E : Type*} [LinearOrder V] {k : ℕ}
    {G : CopiedGraph V E} {F : Finset E} {I J : Finset V}
    (hroot : G.IsRootedForest (I : Set V) F) (hI : I.card = k) (hJ : J.card = k)
    (π : Equiv.Perm (Fin k))
    (hπ : ∀ r, G.reaches F (I.orderEmbOfFin hI r) (J.orderEmbOfFin hJ (π r))) :
    G.IsRootedForest (J : Set V) F := by
  let i := (I.orderIsoOfFin hI).toEquiv
  let j := (J.orderIsoOfFin hJ).toEquiv
  let e : (I : Set V) ≃ (J : Set V) := i.symm.trans (π.trans j)
  apply hroot.of_rootEquiv e
  intro r
  have h := hπ (i.symm r)
  change G.reaches F (i (i.symm r)).val (e r).val at h
  simpa only [i.apply_symm_apply] using h

/-- The actual ordered augmentation of a root-covered copied graph has unit determinant. -/
theorem isUnit_det_appendRootColumns_incidence {d k : ℕ} {E : Type*}
    (G : CopiedGraph (Fin (d + k)) E) (F : Finset E) (q : Fin d ≃ F)
    (I : Finset (Fin (d + k))) (hI : I.card = k)
    (hcover : ∀ x, ∃ r ∈ I, G.reaches F x r) :
    IsUnit (Matrix.appendRootColumns
      (fun x j => G.incidenceColumn (q j).val x) I hI).det := by
  let i := (I.orderIsoOfFin hI).toEquiv
  let e : Fin (d + k) ≃ F ⊕ I :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr q i)
  convert G.isUnit_det_augmentedIncidence F I e hcover using 1
  congr 1
  ext x j
  refine Fin.addCases (fun a => ?_) (fun r => ?_) j
  · simp only [Matrix.appendRootColumns_castAdd, Matrix.submatrix_apply, id_eq,
      e, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
      augmentedIncidence, Sum.map_inl, Sum.elim_inl]
  · simp only [Matrix.appendRootColumns_natAdd, Matrix.submatrix_apply, id_eq,
      e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
      augmentedIncidence, Sum.map_inr, Sum.elim_inr, unitColumn]
    have hi : (i r).val = I.orderEmbOfFin hI r := Finset.coe_orderIsoOfFin_apply I hI r
    rw [hi]
    split_ifs <;> rfl

/-- **Paired incidence signs.** The product of the two literal ordered minors is the root-label parity times matching sign. -/
theorem paired_incidence_minor_sign {d k : ℕ} {E : Type*}
    (G : CopiedGraph (Fin (d + k)) E) (F : Finset E) (q : Fin d ≃ F)
    (I J : Finset (Fin (d + k))) (hI : I.card = k) (hJ : J.card = k)
    (hroot : G.IsRootedForest (I : Set (Fin (d + k))) F)
    (π : Equiv.Perm (Fin k))
    (hπ : ∀ r, G.reaches F (I.orderEmbOfFin hI r) (J.orderEmbOfFin hJ (π r))) :
    let A : Matrix (Fin (d + k)) (Fin d) ℤ := fun x j => G.incidenceColumn (q j).val x
    (A.submatrix (Iᶜ.orderEmbOfFin (show Iᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel])) id).det *
      (A.submatrix (Jᶜ.orderEmbOfFin (show Jᶜ.card = d by
        rw [Finset.card_compl, Fintype.card_fin, hJ, Nat.add_sub_cancel])) id).det =
      (-1 : ℤ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ))) *
        (Equiv.Perm.sign π : ℤ) := by
  let A : Matrix (Fin (d + k)) (Fin d) ℤ := fun x j => G.incidenceColumn (q j).val x
  let irow := Iᶜ.orderEmbOfFin (show Iᶜ.card = d by
    rw [Finset.card_compl, Fintype.card_fin, hI, Nat.add_sub_cancel])
  let jrow := Jᶜ.orderEmbOfFin (show Jᶜ.card = d by
    rw [Finset.card_compl, Fintype.card_fin, hJ, Nat.add_sub_cancel])
  let mi := (A.submatrix irow id).det
  let mj := (A.submatrix jrow id).det
  change mi * mj = _
  have hrange : Set.range A.col = Set.range (fun f : F => G.incidenceColumn f.val) := by
    ext c
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨q j, rfl⟩
    · rintro ⟨f, rfl⟩
      refine ⟨q.symm f, ?_⟩
      change G.incidenceColumn (q (q.symm f)).val = _
      rw [q.apply_symm_apply]
  have hspan : ∀ r, (fun x =>
      (if x = J.orderEmbOfFin hJ (π r) then (1 : ℤ) else 0) -
      (if x = I.orderEmbOfFin hI r then 1 else 0)) ∈
        Submodule.span ℤ (Set.range A.col) := by
    intro r
    rw [hrange]
    have h := (Submodule.span ℤ (Set.range (fun f : F => G.incidenceColumn f.val))).neg_mem
      (G.unitColumn_sub_mem_span_of_reaches F (hπ r))
    rw [neg_sub] at h
    convert h using 1
    ext x
    change _ = unitColumn (J.orderEmbOfFin hJ (π r)) x - unitColumn (I.orderEmbOfFin hI r) x
    unfold unitColumn
    split_ifs <;> rfl
  have hmatch := Matrix.det_appendRootColumns_of_matched_span A I J hI hJ π hspan
  have hJroot := hroot.of_ordered_matching hI hJ π hπ
  have hcoverJ : ∀ x, ∃ r ∈ J, G.reaches F x r := by
    intro x
    obtain ⟨r, hr, hxr, _⟩ := hJroot.2 x
    exact ⟨r, hr, hxr⟩
  have hunit := G.isUnit_det_appendRootColumns_incidence F q J hJ hcoverJ
  change IsUnit (Matrix.appendRootColumns A J hJ).det at hunit
  have hsquare : (Matrix.appendRootColumns A J hJ).det *
      (Matrix.appendRootColumns A J hJ).det = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
  have haug : (Matrix.appendRootColumns A I hI).det *
      (Matrix.appendRootColumns A J hJ).det = (Equiv.Perm.sign π : ℤ) := by
    rw [hmatch, mul_assoc, hsquare, mul_one]
  rw [Matrix.det_appendRootColumns, Matrix.det_appendRootColumns] at haug
  let sI := ∑ x ∈ I, (x : ℕ)
  let sJ := ∑ x ∈ J, (x : ℕ)
  let p := ∑ r : Fin k, (d + (r : ℕ))
  change ((-1 : ℤ) ^ (sI + p) * mi) * ((-1 : ℤ) ^ (sJ + p) * mj) = _ at haug
  have hp : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow]
  have hfactor : (-1 : ℤ) ^ (sI + p) * (-1 : ℤ) ^ (sJ + p) =
      (-1 : ℤ) ^ (sI + sJ) := by
    rw [pow_add, pow_add, pow_add]
    calc
      _ = ((-1 : ℤ) ^ sI * (-1 : ℤ) ^ sJ) * ((-1 : ℤ) ^ p * (-1 : ℤ) ^ p) := by ring
      _ = _ := by rw [hp, mul_one]
  have hsignsquare : (-1 : ℤ) ^ (sI + sJ) * (-1 : ℤ) ^ (sI + sJ) = 1 := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow]
  have heq : (-1 : ℤ) ^ (sI + sJ) *
      (mi * mj) = (Equiv.Perm.sign π : ℤ) := by
    calc
      _ = ((-1 : ℤ) ^ (sI + p) * (-1 : ℤ) ^ (sJ + p)) *
          (mi * mj) := by rw [hfactor]
      _ = _ := by
        convert haug using 1
        ring
  calc
    _ = ((-1 : ℤ) ^ (sI + sJ) * (-1 : ℤ) ^ (sI + sJ)) *
        (mi * mj) := by rw [hsignsquare, one_mul]
    _ = (-1 : ℤ) ^ (sI + sJ) * ((-1 : ℤ) ^ (sI + sJ) *
        (mi * mj)) := by ring
    _ = _ := by rw [heq]

end
end LatticeProb.Graph.CopiedGraph
