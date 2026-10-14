/-
# Atoms of a finite projection determinantal law

The inclusion-determinant identities and nonnegativity determine the atoms of
an orthonormal-column frame. Normalization and support are derived internally.
-/

import LatticeProb.LinearAlgebra.Matrix.CauchyBinet
import LatticeProb.Prob.Determinantal.InclusionNormalization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic



namespace LatticeProb.DPP
open scoped BigOperators Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
/-- Every principal minor of a frame Gram matrix above the column count vanishes. -/
theorem det_principal_gram_eq_zero_of_card_gt {k : ℕ}
    (V : Matrix E (Fin k) ℝ) (A : Finset E) (hA : k < A.card) :
    ((V * V.transpose).submatrix (fun a : A => (a : E))
      (fun a : A => (a : E))).det = 0 := by
  let W : Matrix A (Fin k) ℝ := V.submatrix Subtype.val id
  have hgram : (V * V.transpose).submatrix (fun a : A => (a : E))
      (fun a : A => (a : E)) = W * W.transpose := by
    ext i j
    rfl
  letI : IsEmpty {S : Finset (Fin k) // S.card = Fintype.card A} := ⟨by
    intro S
    have hle := Finset.card_le_univ S.val
    rw [Fintype.card_fin, S.property, Fintype.card_coe] at hle
    exact (Nat.not_le_of_gt hA) hle⟩
  rw [hgram, Matrix.det_mul_eq_sum_subsets W W.transpose
    (fun S => isEmptyElim S)]
  exact Finset.sum_eq_zero (fun S _ => isEmptyElim S)

/-- Nonnegative inclusion sums force all atoms larger than the frame rank to vanish. -/
theorem atom_eq_zero_of_card_gt {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det)
    (S : Finset E) (hS : k < S.card) : p S = 0 := by
  have hn : ∀ T : Finset E,
      0 ≤ Set.indicator {T : Finset E | S ⊆ T} p T := by
    intro T
    exact Set.indicator_nonneg (fun T _ => hp T) T
  have hz := (hdet S).trans (det_principal_gram_eq_zero_of_card_gt V S hS)
  have hle := Finset.single_le_sum (fun T _ => hn T) (Finset.mem_univ S)
  rw [Set.indicator_of_mem (Finset.Subset.refl S) p, hz] at hle
  exact le_antisymm hle (hp S)

/-- A square row minor of a frame, enumerated by the selected finite subset. -/
def frameMinor {k : ℕ} (V : Matrix E (Fin k) ℝ) (S : Finset E)
    (hS : S.card = k) : Matrix (Fin k) (Fin k) ℝ :=
  V.submatrix (fun i => ((S.equivFinOfCardEq hS).symm i).val) id

omit [Fintype E] in
/-- A degree-rank principal Gram determinant is the square of the corresponding row minor. -/
theorem det_principal_gram_eq_sq {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (S : Finset E) (hS : S.card = k) :
    ((V * V.transpose).submatrix (fun a : S => (a : E))
      (fun a : S => (a : E))).det = (frameMinor V S hS).det ^ 2 := by
  let q : Fin k ≃ S := (S.equivFinOfCardEq hS).symm
  let G := (V * V.transpose).submatrix (fun a : S => (a : E))
    (fun a : S => (a : E))
  have he : G.submatrix q q = frameMinor V S hS * (frameMinor V S hS).transpose := by
    ext i j
    rfl
  calc
    G.det = (G.submatrix q q).det := (Matrix.det_submatrix_equiv_self q G).symm
    _ = (frameMinor V S hS).det ^ 2 := by
      rw [he, Matrix.det_mul, Matrix.det_transpose, pow_two]

/-- At the frame rank the inclusion identity equals the atom, since every larger atom vanishes. -/
theorem atom_eq_sq_of_card_eq {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det)
    (S : Finset E) (hS : S.card = k) : p S = (frameMinor V S hS).det ^ 2 := by
  have hatom : (∑ T, Set.indicator {T : Finset E | S ⊆ T} p T) = p S := by
    rw [Finset.sum_eq_single S]
    · exact Set.indicator_of_mem (Finset.Subset.refl S) p
    · intro T _ hTS
      by_cases hST : S ⊆ T
      · rw [Set.indicator_of_mem hST p]
        apply atom_eq_zero_of_card_gt V p hp hdet T
        by_contra hle
        have hcard : T.card ≤ S.card := hS.symm ▸ Nat.le_of_not_gt hle
        exact hTS (Finset.eq_of_subset_of_card_le hST hcard).symm
      · exact Set.indicator_of_notMem hST p
    · intro hn
      exact (hn (Finset.mem_univ S)).elim
  rw [← hatom, hdet S]
  exact det_principal_gram_eq_sq V S hS

omit [DecidableEq E] in
/-- The squared rank-degree row minors of an orthonormal-column frame sum to one. -/
theorem sum_sq_frameMinor_eq_one {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (hV : V.transpose * V = 1) :
    (∑ S : {S : Finset E // S.card = k}, (frameMinor V S.val S.property).det ^ 2) = 1 := by
  let q : ∀ S : {S : Finset E // S.card = Fintype.card (Fin k)}, Fin k ≃ S.val :=
    fun S => (S.val.equivFinOfCardEq (S.property.trans (Fintype.card_fin k))).symm
  have hcb := Matrix.det_mul_eq_sum_subsets V.transpose V q
  rw [hV, Matrix.det_one] at hcb
  have hs : (∑ S : {S : Finset E // S.card = Fintype.card (Fin k)},
      (V.transpose.submatrix id (fun i => (q S i).val)).det *
        (V.submatrix (fun i => (q S i).val) id).det) =
      ∑ S : {S : Finset E // S.card = Fintype.card (Fin k)},
        (frameMinor V S.val (S.property.trans (Fintype.card_fin k))).det ^ 2 := by
    apply Finset.sum_congr rfl
    intro S _
    change (frameMinor V S.val (S.property.trans (Fintype.card_fin k))).transpose.det *
      (frameMinor V S.val (S.property.trans (Fintype.card_fin k))).det = _
    rw [Matrix.det_transpose, pow_two]
  let e : {S : Finset E // S.card = k} ≃
      {S : Finset E // S.card = Fintype.card (Fin k)} :=
    { toFun := fun S => ⟨S.val, S.property.trans (Fintype.card_fin k).symm⟩
      invFun := fun S => ⟨S.val, S.property.trans (Fintype.card_fin k)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (e.sum_comp (fun S =>
    (frameMinor V S.val (S.property.trans (Fintype.card_fin k))).det ^ 2)).trans
      (hs.symm.trans hcb.symm)

/-- The rank-degree atoms carry the whole mass of an orthonormal-frame inclusion law. -/
theorem sum_rank_atoms_eq_one {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (hV : V.transpose * V = 1) (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det) :
    (∑ S : {S : Finset E // S.card = k}, p S.val) = 1 := by
  calc
    (∑ S : {S : Finset E // S.card = k}, p S.val) =
        ∑ S : {S : Finset E // S.card = k}, (frameMinor V S.val S.property).det ^ 2 :=
      Finset.sum_congr rfl (fun S _ => atom_eq_sq_of_card_eq V p hp hdet S.val S.property)
    _ = 1 := sum_sq_frameMinor_eq_one V hV

/-- Every atom outside the column count vanishes, including all smaller subsets. -/
theorem atom_eq_zero_of_card_ne {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (hV : V.transpose * V = 1) (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det)
    (S : Finset E) (hS : S.card ≠ k) : p S = 0 := by
  have hn := LatticeProb.DPP.sum_eq_one_of_inclusion_minors (V * V.transpose) p hdet
  have hk := sum_rank_atoms_eq_one V hV p hp hdet
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun T : Finset E => T.card = k) p
  rw [hk, hn, add_eq_left] at hpart
  have hle := Finset.single_le_sum
    (fun T (_ : T ∈ (Finset.univ : Finset {T : Finset E // T.card ≠ k})) => hp T.val)
    (Finset.mem_univ (⟨S, hS⟩ : {T : Finset E // T.card ≠ k}))
  rw [hpart] at hle
  exact le_antisymm hle (hp S)

/-- **Projection DPP atom formula.** The original inclusion law on all subsets
of a real orthonormal-column frame has squared determinant atoms at its column
count and zero atoms at every other degree. -/
theorem atom_formula_of_orthonormal_frame {k : ℕ} (V : Matrix E (Fin k) ℝ)
    (hV : V.transpose * V = 1) (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det) :
    (∀ S : Finset E, ∀ hS : S.card = k, p S = (frameMinor V S hS).det ^ 2) ∧
      (∀ S : Finset E, S.card ≠ k → p S = 0) :=
  ⟨atom_eq_sq_of_card_eq V p hp hdet, atom_eq_zero_of_card_ne V hV p hp hdet⟩

end
end LatticeProb.DPP
