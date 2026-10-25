module

/-
# Orthogonal annihilation of determinant coefficients

Contraction is determinant row linearity. Orthogonality produces a zero row;
terms from occupied coordinates vanish by repeated rows. CAR then recovers the
original coefficient vector after creation by a unit orthogonal vector.
-/

public import LatticeProb.LinearAlgebra.DeterminantCreation
public import LatticeProb.LinearAlgebra.FinsetCAR

@[expose] public section



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical Matrix
noncomputable section

/-- In occupation-bit coordinates the extended frame coefficients are exactly
the signed creation operator, at every subset degree. -/
theorem determinantCoeff_prependColumn_eq_create {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (b : Fin n → Bool) :
    determinantCoeff (prependColumn u V) (bitsFinsetEquiv n b) =
      create n u (fun t => determinantCoeff V (bitsFinsetEquiv n t)) b := by
  rw [← finsetCreate_bits]
  exact determinantCoeff_prependColumn u V (bitsFinsetEquiv n b)

private theorem det_cons_rows_zero_of_mem {n d : ℕ}
    (V : Matrix (Fin n) (Fin (d + 1)) ℝ) (S : Finset (Fin n))
    (hS : S.card = d) (i : Fin n) (hi : i ∈ S) :
    (V.submatrix (Fin.cons i (S.orderEmbOfFin hS)) id).det = 0 := by
  let q := (S.orderIsoOfFin hS).symm ⟨i, hi⟩
  have hqi : S.orderEmbOfFin hS q = i :=
    congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply ⟨i, hi⟩)
  apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero q).symm
  funext j
  simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ, hqi]

/-- Orthogonality to every frame column makes all signed contraction
coefficients vanish. No annihilation identity is assumed. -/
theorem finsetContract_determinantCoeff_eq_zero {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (horth : ∀ j, ∑ i, u i * V i j = 0) :
    finsetContract u (determinantCoeff V) = 0 := by
  funext S
  change finsetContract u (determinantCoeff V) S = 0
  by_cases hdeg : S.card + 1 = k
  · obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨S.card, hdeg.symm⟩
    have hS : S.card = d := Nat.add_right_cancel hdeg
    let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
      Fin.cons (0 : Fin (d + 1) → ℝ)
        (fun j => V (S.orderEmbOfFin hS j))
    have hrow (i : Fin n) : M.updateRow 0 (V i) =
        V.submatrix (Fin.cons i (S.orderEmbOfFin hS)) id := by
      ext a b
      cases a using Fin.cases with
      | zero => simp only [Matrix.updateRow_self, Matrix.submatrix_apply, Fin.cons_zero, id_eq]
      | succ a =>
        rw [Matrix.updateRow_ne (Fin.succ_ne_zero a)]
        rfl
    have hcoeff (i : Fin n) : (if i ∈ S then 0 else
        insertionSign S i * u i * determinantCoeff V (insert i S)) =
        u i * (M.updateRow 0 (V i)).det := by
      rw [hrow]
      by_cases hi : i ∈ S
      · rw [if_pos hi, det_cons_rows_zero_of_mem V S hS i hi, mul_zero]
      · rw [if_neg hi, det_cons_rows_eq_insertionSign V S hS i hi]
        rw [mul_assoc, mul_left_comm]
    rw [finsetContract]
    simp only [hcoeff]
    rw [LatticeProb.LinearAlgebra.sum_mul_det_update_row]
    have hz : (∑ i : Fin n, u i • V i) = 0 := by
      funext j
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using horth j
    rw [hz]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    simp only [Matrix.updateRow_self, Pi.zero_apply]
  · rw [finsetContract]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · rfl
    · have hcard : (insert i S).card ≠ k := by
        rwa [Finset.card_insert_of_notMem hi]
      rw [determinantCoeff_of_card_ne V _ hcard, mul_zero]

/-- **Exact orthogonal recovery.** Contracting the graded coefficients of the
first-column extension by a unit vector perpendicular to the frame recovers
its original graded coefficients, with no degree-dependent sign. -/
theorem finsetContract_prependColumn {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (hunit : ∑ i, u i ^ 2 = 1)
    (horth : ∀ j, ∑ i, u i * V i j = 0) :
    finsetContract u (determinantCoeff (prependColumn u V)) = determinantCoeff V := by
  have hc : determinantCoeff (prependColumn u V) = finsetCreate u (determinantCoeff V) := by
    funext S
    exact determinantCoeff_prependColumn u V S
  funext S
  have h := finsetContract_create_add_create_contract u (determinantCoeff V) S
  rw [finsetContract_determinantCoeff_eq_zero u V horth, show finsetCreate u (0 : Finset (Fin n) → ℝ) = 0 from finsetCreate_zero u,
    Pi.zero_apply, add_zero, hunit, one_mul] at h
  rw [hc]
  exact h

end
end LatticeProb.SubsetContraction
