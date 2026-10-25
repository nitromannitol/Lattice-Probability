module

/-
# Finset and determinant coordinates for signed contraction

The sharp subset coefficient estimate is transported to ordinary finsets. The
sign is the number of smaller elements. The determinant formula uses the
increasing enumeration of each subset of the required size; other degrees have
zero exterior coefficient.
-/

public import LatticeProb.LinearAlgebra.SubsetContraction
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section



namespace LatticeProb.SubsetContraction

open scoped BigOperators Matrix

/-- Occupation bits correspond to the finite set of their true coordinates. -/
def bitsFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun b := Finset.univ.filter (fun i => b i = true)
  invFun S := fun i => decide (i ∈ S)
  left_inv b := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases b i <;> rfl
  right_inv S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- Membership in the finset is exactly truth of its occupation bit. -/
theorem mem_bitsFinsetEquiv (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    i ∈ bitsFinsetEquiv n b ↔ b i = true := by
  change i ∈ Finset.univ.filter (fun j => b j = true) ↔ b i = true
  rw [Finset.mem_filter, and_iff_right (Finset.mem_univ i)]

/-- Setting an occupation bit to true is ordinary finset insertion. -/
theorem bitsFinsetEquiv_update (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    bitsFinsetEquiv n (Function.update b i true) = insert i (bitsFinsetEquiv n b) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [mem_bitsFinsetEquiv, Function.update_self, Finset.mem_insert,
      true_or, eq_self]
  · simp only [mem_bitsFinsetEquiv, Function.update_apply, hji, ↓reduceIte,
      Finset.mem_insert, false_or]

/-- Clearing an occupation bit is ordinary finset erasure. -/
theorem bitsFinsetEquiv_update_false (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    bitsFinsetEquiv n (Function.update b i false) = (bitsFinsetEquiv n b).erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [mem_bitsFinsetEquiv, Function.update_self, Bool.false_eq_true,
      Finset.mem_erase, ne_eq, not_true_eq_false, false_and]
  · simp only [mem_bitsFinsetEquiv, Function.update_apply, hji, ↓reduceIte,
      Finset.mem_erase, ne_eq, not_false_eq_true, true_and]

/-- The order sign of inserting `i` into `S` is `(-1)` to the number of members
of `S` strictly below `i`. -/
def insertionSign {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  (-1 : ℝ) ^ (∑ j : Fin n, if j < i ∧ j ∈ S then 1 else 0)

/-- The insertion sign is `(-1)` raised to the cardinality of the smaller
members of the subset. -/
theorem insertionSign_eq_pow_card_filter {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    insertionSign S i = (-1 : ℝ) ^ (S.filter (fun j => j < i)).card := by
  have hfilter : (Finset.univ.filter (fun j : Fin n => j < i ∧ j ∈ S)) =
      S.filter (fun j => j < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  rw [insertionSign, Finset.sum_boole, hfilter, Nat.cast_id]

/-- The matrix sign equals the ordinary ordered finset insertion sign. -/
theorem koszulSign_eq_insertionSign (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    koszulSign n b i = insertionSign (bitsFinsetEquiv n b) i := by
  rw [koszulSign_eq_pow]
  simp only [insertionSign, mem_bitsFinsetEquiv]

/-- **Finite subset contraction bound.** The signed contraction of arbitrary
finset coefficients has squared energy at most `∑ u²` times their squared energy. -/
theorem sum_sq_finset_contraction_le (n : ℕ) (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), (∑ i : Fin n, if i ∈ S then 0 else
      insertionSign S i * u i * x (insert i S)) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ S : Finset (Fin n), x S ^ 2 := by
  have h := sum_sq_signed_insertion_le n u (fun b => x (bitsFinsetEquiv n b))
  simp only [koszulSign_eq_insertionSign, bitsFinsetEquiv_update,
    ← mem_bitsFinsetEquiv] at h
  rw [(bitsFinsetEquiv n).sum_comp (fun S =>
    (∑ i : Fin n, if i ∈ S then 0 else insertionSign S i * u i * x (insert i S)) ^ 2),
    (bitsFinsetEquiv n).sum_comp (fun S => x S ^ 2)] at h
  exact h

/-- The degree-`k` determinant coefficient of a rectangular matrix, with rows in
increasing subset order. All other degrees have zero coefficient. -/
def determinantCoeff {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (S : Finset (Fin n)) : ℝ :=
  if h : S.card = k then (V.submatrix (S.orderEmbOfFin h) id).det else 0

/-- On the correct degree, the coefficient is the literal ordered minor. -/
theorem determinantCoeff_of_card_eq {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (S : Finset (Fin n)) (h : S.card = k) :
    determinantCoeff V S = (V.submatrix (S.orderEmbOfFin h) id).det := by
  rw [determinantCoeff, dif_pos h]

/-- Away from its degree, a determinant coefficient is zero. -/
theorem determinantCoeff_of_card_ne {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (S : Finset (Fin n)) (h : S.card ≠ k) : determinantCoeff V S = 0 := by
  rw [determinantCoeff, dif_neg h]

/-- The signed insertion sum of determinant coefficients satisfies the sharp
contraction estimate after arbitrary masking by a family of subsets. -/
theorem sum_sq_masked_determinant_contraction_le {n k : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (u : Fin n → ℝ)
    (A : Set (Finset (Fin n))) :
    (∑ S : Finset (Fin n), (∑ i : Fin n, if i ∈ S then 0 else
      insertionSign S i * u i * (A.indicator (determinantCoeff V)) (insert i S)) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ S : Finset (Fin n), (A.indicator (determinantCoeff V) S) ^ 2 :=
  sum_sq_finset_contraction_le n u (A.indicator (determinantCoeff V))

/-- **Finite subset creator bound.** The signed deletion sum has squared energy
at most `∑ u²` times the input coefficient energy. -/
theorem sum_sq_finset_creation_le (n : ℕ) (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), (∑ i : Fin n, if i ∈ S then
      insertionSign S i * u i * x (S.erase i) else 0) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ S : Finset (Fin n), x S ^ 2 := by
  have h := sum_sq_signed_deletion_le n u (fun b => x (bitsFinsetEquiv n b))
  simp only [koszulSign_eq_insertionSign, bitsFinsetEquiv_update_false,
    ← mem_bitsFinsetEquiv] at h
  rw [(bitsFinsetEquiv n).sum_comp (fun S =>
    (∑ i : Fin n, if i ∈ S then insertionSign S i * u i * x (S.erase i) else 0) ^ 2),
    (bitsFinsetEquiv n).sum_comp (fun S => x S ^ 2)] at h
  exact h

/-- The ordered deletion sum of arbitrarily masked determinant coefficients has
the sharp creator bound. Every input coefficient is the actual ordered minor. -/
theorem sum_sq_masked_determinant_creation_le {n k : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (u : Fin n → ℝ)
    (A : Set (Finset (Fin n))) :
    (∑ S : Finset (Fin n), (∑ i : Fin n, if i ∈ S then
      insertionSign S i * u i * (A.indicator (determinantCoeff V)) (S.erase i)
      else 0) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ S : Finset (Fin n), (A.indicator (determinantCoeff V) S) ^ 2 :=
  sum_sq_finset_creation_le n u (A.indicator (determinantCoeff V))

/-- On a subset of degree `k+1`, every deleted-coordinate coefficient is the
literal increasing-order `k`-row determinant; its cardinality is derived. -/
theorem determinantCoeff_erase {n k : ℕ} (V : Matrix (Fin n) (Fin k) ℝ)
    (S : Finset (Fin n)) (hS : S.card = k + 1) (i : Fin n) (hi : i ∈ S) :
    determinantCoeff V (S.erase i) =
      (V.submatrix ((S.erase i).orderEmbOfFin (by
        rw [Finset.card_erase_of_mem hi, hS, Nat.add_sub_cancel])) id).det := by
  apply determinantCoeff_of_card_eq

end LatticeProb.SubsetContraction
