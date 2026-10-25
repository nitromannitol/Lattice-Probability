module

/-
# Ordered determinant coordinates for projection DPP atoms

The atom formula is independent of the enumeration of a selected row subset.
It therefore identifies the actual inclusion law with the squared coefficients
used by ordered finite-subset contraction.
-/

public import LatticeProb.Prob.DPP.FrameCarrier
public import LatticeProb.LinearAlgebra.FiniteSubsetContraction

@[expose] public section



namespace LatticeProb.DPP
open scoped BigOperators Classical
noncomputable section

/-- The square of a selected frame minor is independent of its row enumeration. -/
theorem det_row_minor_sq_eq {E : Type*} [DecidableEq E] {k : ℕ}
    (V : Matrix E (Fin k) ℝ) (S : Finset E) (q q' : Fin k ≃ S) :
    (V.submatrix (fun i => (q i).val) id).det ^ 2 =
      (V.submatrix (fun i => (q' i).val) id).det ^ 2 := by
  have h := Matrix.det_submatrix_mul_det_submatrix_eq V.transpose V S q q'
  change (V.submatrix (fun i => (q i).val) id).transpose.det *
      (V.submatrix (fun i => (q i).val) id).det =
    (V.submatrix (fun i => (q' i).val) id).transpose.det *
      (V.submatrix (fun i => (q' i).val) id).det at h
  simpa only [Matrix.det_transpose, pow_two] using h

/-- The actual atom at the frame degree is the squared row determinant in any enumeration. -/
theorem atom_eq_sq_of_enumeration {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (V : Matrix E (Fin k) ℝ) (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : E))
        (fun a : A => (a : E))).det)
    (S : Finset E) (hS : S.card = k) (q : Fin k ≃ S) :
    p S = (V.submatrix (fun i => (q i).val) id).det ^ 2 :=
  (atom_eq_sq_of_card_eq V p hp hdet S hS).trans
    (det_row_minor_sq_eq V S (S.equivFinOfCardEq hS).symm q)

/-- **Ordered atom identification.** Every atom of the original nonnegative
inclusion law equals the squared increasing-order determinant coefficient.
Both the degree restriction and normalization are derived from that law. -/
theorem atom_eq_determinantCoeff_sq {n k : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : V.transpose * V = 1)
    (p : Finset (Fin n) → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset (Fin n), ∑ S, Set.indicator {S : Finset (Fin n) | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : Fin n))
        (fun a : A => (a : Fin n))).det)
    (S : Finset (Fin n)) : p S = LatticeProb.SubsetContraction.determinantCoeff V S ^ 2 := by
  by_cases hS : S.card = k
  · rw [LatticeProb.SubsetContraction.determinantCoeff_of_card_eq V S hS]
    exact atom_eq_sq_of_enumeration V p hp hdet S hS (S.orderIsoOfFin hS).toEquiv
  · rw [LatticeProb.SubsetContraction.determinantCoeff_of_card_ne V S hS,
      zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact atom_eq_zero_of_card_ne V hV p hp hdet S hS

/-- An event's probability is the squared energy of the masked ordered determinant
coefficients, for the actual law given by the original inclusion identities. -/
theorem event_mass_eq_masked_determinant_energy {n k : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (hV : V.transpose * V = 1)
    (p : Finset (Fin n) → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset (Fin n), ∑ S, Set.indicator {S : Finset (Fin n) | A ⊆ S} p S =
      ((V * V.transpose).submatrix (fun a : A => (a : Fin n))
        (fun a : A => (a : Fin n))).det)
    (ev : Set (Finset (Fin n))) :
    (∑ S, Set.indicator ev p S) =
      ∑ S, (Set.indicator ev (LatticeProb.SubsetContraction.determinantCoeff V) S) ^ 2 := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ∈ ev
  · rw [Set.indicator_of_mem hS p,
      Set.indicator_of_mem hS (LatticeProb.SubsetContraction.determinantCoeff V)]
    exact atom_eq_determinantCoeff_sq V hV p hp hdet S
  · rw [Set.indicator_of_notMem hS p,
      Set.indicator_of_notMem hS (LatticeProb.SubsetContraction.determinantCoeff V),
      zero_pow (by decide : (2 : ℕ) ≠ 0)]

end
end LatticeProb.DPP
