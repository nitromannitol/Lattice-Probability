module

/-
# Finite-set frame atom formula on the original carrier

An arbitrary finite carrier is enumerated internally by `Fintype.equivFin`.
No support, normalization, or atom identity is supplied by the caller.
-/

public import LatticeProb.Prob.DPP.FrameAtoms

@[expose] public section



namespace LatticeProb.DPP
open scoped BigOperators Classical
noncomputable section

/-- **Original-carrier frame atoms.** A real frame on `Fin (card E)` is pulled
back along the internally chosen finite-carrier equivalence. The literal
original inclusion-determinant law gives all atoms and normalization. -/
theorem original_carrier_atom_formula_of_frame
    {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (Q : Matrix E E ℝ) (V : Matrix (Fin (Fintype.card E)) (Fin k) ℝ)
    (hV : V.transpose * V = 1)
    (hQ : Q = (V * V.transpose).submatrix (Fintype.equivFin E) (Fintype.equivFin E))
    (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      (Q.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    (∀ S : Finset E, ∀ hS : S.card = k,
      p S = (frameMinor (V.submatrix (Fintype.equivFin E) id) S hS).det ^ 2) ∧
    (∀ S : Finset E, S.card ≠ k → p S = 0) ∧ (∑ S, p S = 1) := by
  let e := Fintype.equivFin E
  let W : Matrix E (Fin k) ℝ := V.submatrix e id
  have hW : W.transpose * W = 1 := by
    change V.transpose.submatrix id e * V.submatrix e id = 1
    rw [Matrix.submatrix_mul_equiv V.transpose V id e id, hV,
      Matrix.submatrix_id_id]
  have hQW : Q = W * W.transpose := by
    rw [hQ]
    ext i j
    rfl
  have hdetW : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((W * W.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det := by
    intro A
    rw [← hQW]
    exact hdet A
  obtain ⟨hdegree, hoff⟩ := atom_formula_of_orthonormal_frame W hW p hp hdetW
  exact ⟨hdegree, hoff, LatticeProb.DPP.sum_eq_one_of_inclusion_minors Q p hdet⟩

/-- A frame on an arbitrary finite carrier has the same column inner products
after transport to its internally enumerated finite coordinate carrier. -/
theorem transpose_mul_equivFin_frame
    {E : Type*} [Fintype E] {k : ℕ} (W : Matrix E (Fin k) ℝ) :
    (W.submatrix (Fintype.equivFin E).symm id).transpose *
      W.submatrix (Fintype.equivFin E).symm id = W.transpose * W := by
  change W.transpose.submatrix id (Fintype.equivFin E).symm *
    W.submatrix (Fintype.equivFin E).symm id = _
  rw [Matrix.submatrix_mul_equiv W.transpose W id (Fintype.equivFin E).symm id,
    Matrix.submatrix_id_id]

end
end LatticeProb.DPP
