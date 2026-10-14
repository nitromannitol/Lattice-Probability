/-
# Signed contraction on finite subset coefficients

The subset coefficient space is built by splitting at the first coordinate.
Its annihilation matrix has blocks `[[C, a I], [0, -C]]`. The canonical
anticommutation identity gives the sharp square-sum contraction bound.
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin



namespace LatticeProb.SubsetContraction

open scoped BigOperators Matrix

/-- Subsets of an ordered `n`-element set, split by absence or presence of its
first element. The empty set is the sole index in dimension zero. -/
abbrev SubsetIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => SubsetIndex n ⊕ SubsetIndex n

/-- Every recursively indexed finite subset space is finite. -/
instance subsetIndexFintype : (n : ℕ) → Fintype (SubsetIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI := subsetIndexFintype n
    inferInstanceAs (Fintype (SubsetIndex n ⊕ SubsetIndex n))

/-- Equality of recursively indexed finite subsets is decidable. -/
instance subsetIndexDecidableEq : (n : ℕ) → DecidableEq (SubsetIndex n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI := subsetIndexDecidableEq n
    inferInstanceAs (DecidableEq (SubsetIndex n ⊕ SubsetIndex n))

/-- Annihilation by `u`, with the Koszul sign from passing the first occupied
coordinate. Rows index the output subset and columns index the input subset. -/
def annihilation : (n : ℕ) → (Fin n → ℝ) → Matrix (SubsetIndex n) (SubsetIndex n) ℝ
  | 0, _ => 0
  | n + 1, u => Matrix.fromBlocks (annihilation n (fun i => u i.succ))
      (u 0 • 1) 0 (-annihilation n (fun i => u i.succ))

private theorem block_car {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (a : ℝ) :
    let B := Matrix.fromBlocks C (a • 1) 0 (-C)
    B * Bᵀ + Bᵀ * B = Matrix.fromBlocks
      (C * Cᵀ + Cᵀ * C + a ^ 2 • 1) 0 0
      (C * Cᵀ + Cᵀ * C + a ^ 2 • 1) := by
  dsimp only
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_zero, Matrix.transpose_neg, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, smul_neg, neg_zero, neg_add_cancel]
  congr 1
  · rw [← pow_two]
    exact add_right_comm _ _ _
  · rw [← pow_two, add_assoc]
    congr 1
    exact add_comm _ _

/-- **Canonical anticommutation identity.** Annihilation and its transpose satisfy
`C Cᵀ + Cᵀ C = (∑ i, u i²) I`, in every finite dimension, including zero. -/
theorem annihilation_car (n : ℕ) (u : Fin n → ℝ) :
    annihilation n u * (annihilation n u)ᵀ +
      (annihilation n u)ᵀ * annihilation n u = (∑ i, u i ^ 2) • 1 := by
  induction n with
  | zero => simp only [annihilation, Matrix.transpose_zero, Matrix.zero_mul, add_zero,
      Finset.univ_eq_empty, Finset.sum_empty, zero_smul]
  | succ n ih =>
    simp only [annihilation]
    rw [block_car, ih, ← add_smul, Fin.sum_univ_succ]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
    congr 1 <;> rw [add_comm]

/-- The sum of the annihilator and creator squared energies is the coefficient
energy multiplied by the squared length of `u`. -/
theorem annihilation_energy_identity (n : ℕ) (u : Fin n → ℝ)
    (x : SubsetIndex n → ℝ) :
    (∑ s, (annihilation n u *ᵥ x) s ^ 2) +
      (∑ s, ((annihilation n u)ᵀ *ᵥ x) s ^ 2) =
      (∑ i, u i ^ 2) * ∑ s, x s ^ 2 := by
  have he := congrArg (fun M : Matrix (SubsetIndex n) (SubsetIndex n) ℝ =>
    x ⬝ᵥ (M *ᵥ x)) (annihilation_car n u)
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec] at he
  have ht := Matrix.dotProduct_transpose_mulVec (annihilation n u)ᵀ x
    ((annihilation n u)ᵀ *ᵥ x)
  rw [Matrix.transpose_transpose] at ht
  rw [ht, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at he
  simpa only [dotProduct, pow_two, add_comm] using he

/-- Signed contraction on all subset coefficients has square-sum operator bound
`∑ (C_u x)² ≤ (∑ u²) (∑ x²)`. No norm bound is assumed. -/
theorem sum_sq_annihilation_le (n : ℕ) (u : Fin n → ℝ)
    (x : SubsetIndex n → ℝ) :
    (∑ s, (annihilation n u *ᵥ x) s ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ s, x s ^ 2 := by
  calc
    _ ≤ (∑ s, (annihilation n u *ᵥ x) s ^ 2) +
        (∑ s, ((annihilation n u)ᵀ *ᵥ x) s ^ 2) :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun s _ => sq_nonneg _)
    _ = _ := annihilation_energy_identity n u x

/-- The occupation bits of a recursive subset index, in increasing coordinate order. -/
def toBits : (n : ℕ) → SubsetIndex n → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, Sum.inl s => Fin.cons false (toBits n s)
  | n + 1, Sum.inr s => Fin.cons true (toBits n s)

/-- The recursive subset index with the given occupation bits. -/
def ofBits : (n : ℕ) → (Fin n → Bool) → SubsetIndex n
  | 0, _ => ()
  | n + 1, b => if b 0 then Sum.inr (ofBits n (Fin.tail b))
      else Sum.inl (ofBits n (Fin.tail b))

/-- Converting an index to occupation bits and back preserves the index. -/
theorem ofBits_toBits (n : ℕ) (s : SubsetIndex n) : ofBits n (toBits n s) = s := by
  induction n with
  | zero => cases s; rfl
  | succ n ih =>
    cases s <;> simp only [toBits, ofBits, Fin.cons_zero, Fin.tail_cons,
      Bool.false_eq_true, ↓reduceIte, ih]

/-- Converting occupation bits to an index and back preserves every coordinate. -/
theorem toBits_ofBits (n : ℕ) (b : Fin n → Bool) : toBits n (ofBits n b) = b := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    cases hb : b 0 <;> simp only [ofBits, hb, Bool.false_eq_true,
      ↓reduceIte, toBits, ih]
    · rw [← hb]; exact Fin.cons_self_tail b
    · rw [← hb]; exact Fin.cons_self_tail b

/-- Subset indices are exactly Bool-valued subsets of `Fin n`. -/
def bitsEquiv (n : ℕ) : SubsetIndex n ≃ (Fin n → Bool) where
  toFun := toBits n
  invFun := ofBits n
  left_inv := ofBits_toBits n
  right_inv := toBits_ofBits n

/-- Ordered subset contraction, transported along the explicit occupation-bit
bijection. Its input and output are coefficients of actual subsets. -/
def contract (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (b : Fin n → Bool) : ℝ :=
  (annihilation n u *ᵥ (fun s => x (toBits n s))) (ofBits n b)

/-- The recursive matrix action equals its Bool-subset coordinate action. -/
theorem contract_toBits (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (s : SubsetIndex n) :
    contract n u x (toBits n s) =
      (annihilation n u *ᵥ (fun t => x (toBits n t))) s := by
  rw [contract, ofBits_toBits]

/-- Transport to Bool-subset coefficients preserves the squared coefficient sum. -/
theorem sum_sq_toBits (n : ℕ) (x : (Fin n → Bool) → ℝ) :
    (∑ s, x (toBits n s) ^ 2) = ∑ b, x b ^ 2 :=
  (bitsEquiv n).sum_comp (fun b => x b ^ 2)

/-- **Subset coordinate contraction bound.** For arbitrary real coefficients of
Bool-valued subsets, `∑ (C_u x)² ≤ (∑ u²) (∑ x²)`. -/
theorem sum_sq_contract_le (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ) :
    (∑ b, contract n u x b ^ 2) ≤ (∑ i, u i ^ 2) * ∑ b, x b ^ 2 := by
  have h := sum_sq_annihilation_le n u (fun s => x (toBits n s))
  rw [← sum_sq_toBits n (contract n u x)]
  rw [sum_sq_toBits] at h
  simpa only [contract_toBits] using h

/-- On a subset missing the first coordinate, contraction splits into tail
contraction and insertion of the first coordinate with positive sign. -/
theorem contract_cons_false (n : ℕ) (u : Fin (n + 1) → ℝ)
    (x : (Fin (n + 1) → Bool) → ℝ) (b : Fin n → Bool) :
    contract (n + 1) u x (Fin.cons false b) =
      contract n (Fin.tail u) (fun t => x (Fin.cons false t)) b +
        u 0 * x (Fin.cons true b) := by
  simp only [contract, annihilation, ofBits, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, Matrix.fromBlocks_mulVec, Sum.elim_inl,
    Pi.add_apply, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    smul_eq_mul, Function.comp_def, toBits, toBits_ofBits, Fin.tail_def]

/-- On a subset containing the first coordinate, tail contraction acquires a
minus sign from passing that occupied coordinate. -/
theorem contract_cons_true (n : ℕ) (u : Fin (n + 1) → ℝ)
    (x : (Fin (n + 1) → Bool) → ℝ) (b : Fin n → Bool) :
    contract (n + 1) u x (Fin.cons true b) =
      -contract n (Fin.tail u) (fun t => x (Fin.cons true t)) b := by
  simp only [contract, annihilation, ofBits, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Matrix.fromBlocks_mulVec, Sum.elim_inr, Matrix.zero_mulVec,
    zero_add, Matrix.neg_mulVec, Pi.neg_apply, Function.comp_def, toBits,
    Fin.tail_def]

/-- The ordered Koszul sign: start at `+1` and change sign for each occupied
coordinate strictly before the selected coordinate. -/
def koszulSign : (n : ℕ) → (Fin n → Bool) → Fin n → ℝ
  | 0, _, i => Fin.elim0 i
  | n + 1, b, i => Fin.cases 1 (fun j =>
      if b 0 then -koszulSign n (Fin.tail b) j else koszulSign n (Fin.tail b) j) i

/-- The annihilation coordinate is the signed sum of coefficients obtained by
inserting one absent coordinate. The sign is its position in increasing order. -/
theorem contract_eq_sum (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (b : Fin n → Bool) :
    contract n u x b = ∑ i, if b i then 0 else
      koszulSign n b i * u i * x (Function.update b i true) := by
  induction n with
  | zero => simp only [contract, annihilation, Matrix.zero_mulVec, Pi.zero_apply,
      Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    rw [← Fin.cons_self_tail b]
    cases b 0 with
    | false =>
      rw [contract_cons_false, ih, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
        koszulSign, Fin.cases_zero, Fin.cases_succ, Fin.tail_cons, one_mul,
        Fin.update_cons_zero, ← Fin.cons_update]
      exact add_comm _ _
    | true =>
      rw [contract_cons_true, ih, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte, koszulSign,
        Fin.cases_succ, Fin.tail_cons, zero_add, ← Fin.cons_update, neg_mul]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases Fin.tail b i with
      | false => rfl
      | true => exact neg_zero

/-- The creator, the transpose of the annihilator, has the same sharp
square-sum bound. -/
theorem sum_sq_creator_le (n : ℕ) (u : Fin n → ℝ) (x : SubsetIndex n → ℝ) :
    (∑ s, ((annihilation n u)ᵀ *ᵥ x) s ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ s, x s ^ 2 := by
  calc
    _ ≤ (∑ s, (annihilation n u *ᵥ x) s ^ 2) +
        (∑ s, ((annihilation n u)ᵀ *ᵥ x) s ^ 2) :=
      le_add_of_nonneg_left (Finset.sum_nonneg fun s _ => sq_nonneg _)
    _ = _ := annihilation_energy_identity n u x

/-- The explicit ordered insertion sum obeys the sharp squared contraction
bound for every coefficient function, including arbitrarily masked ones. -/
theorem sum_sq_signed_insertion_le (n : ℕ) (u : Fin n → ℝ)
    (x : (Fin n → Bool) → ℝ) :
    (∑ b, (∑ i, if b i then 0 else
      koszulSign n b i * u i * x (Function.update b i true)) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ b, x b ^ 2 := by
  simp only [← contract_eq_sum]
  exact sum_sq_contract_le n u x

/-- The recursive sign is exactly `(-1)` raised to the number of occupied
coordinates before `i`, expressed as a finite indicator sum. -/
theorem koszulSign_eq_pow (n : ℕ) (b : Fin n → Bool) (i : Fin n) :
    koszulSign n b i = (-1 : ℝ) ^ (∑ j, if j < i ∧ b j = true then 1 else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [koszulSign, Fin.cases_zero, Fin.not_lt_zero, false_and,
        ↓reduceIte, Finset.sum_const_zero, pow_zero]
    | succ i =>
      rw [koszulSign, Fin.cases_succ, Fin.sum_univ_succ]
      simp only [Fin.succ_pos, true_and, Fin.succ_lt_succ_iff]
      cases b 0 with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        exact ih (Fin.tail b) i
      | true =>
        simp only [↓reduceIte]
        rw [ih, pow_add, pow_one, neg_one_mul]
        rfl

/-- Creation by `u` on Bool-subset coefficients, the transpose of signed
annihilation under the square-sum inner product. -/
def create (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (b : Fin n → Bool) : ℝ :=
  ((annihilation n u)ᵀ *ᵥ (fun s => x (toBits n s))) (ofBits n b)

/-- Creation transported to occupation bits preserves the matrix coefficient. -/
theorem create_toBits (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (s : SubsetIndex n) :
    create n u x (toBits n s) =
      ((annihilation n u)ᵀ *ᵥ (fun t => x (toBits n t))) s := by
  rw [create, ofBits_toBits]

/-- Creation by one vector has the sharp square-sum bound on actual Bool-subset
coefficients. -/
theorem sum_sq_create_le (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ) :
    (∑ b, create n u x b ^ 2) ≤ (∑ i, u i ^ 2) * ∑ b, x b ^ 2 := by
  have h := sum_sq_creator_le n u (fun s => x (toBits n s))
  rw [← sum_sq_toBits n (create n u x)]
  rw [sum_sq_toBits] at h
  simpa only [create_toBits] using h

/-- Without the first coordinate, creation acts on the tail coefficients. -/
theorem create_cons_false (n : ℕ) (u : Fin (n + 1) → ℝ)
    (x : (Fin (n + 1) → Bool) → ℝ) (b : Fin n → Bool) :
    create (n + 1) u x (Fin.cons false b) =
      create n (Fin.tail u) (fun t => x (Fin.cons false t)) b := by
  simp only [create, annihilation, ofBits, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_mulVec, Sum.elim_inl, Matrix.transpose_zero,
    Matrix.zero_mulVec, add_zero, Function.comp_def, toBits, Fin.tail_def]

/-- Creation of a subset containing the first coordinate is its first-coordinate
term minus the tail creator term. -/
theorem create_cons_true (n : ℕ) (u : Fin (n + 1) → ℝ)
    (x : (Fin (n + 1) → Bool) → ℝ) (b : Fin n → Bool) :
    create (n + 1) u x (Fin.cons true b) =
      u 0 * x (Fin.cons false b) -
        create n (Fin.tail u) (fun t => x (Fin.cons true t)) b := by
  simp only [create, annihilation, ofBits, Fin.cons_zero, Fin.cons_succ,
    ↓reduceIte, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec,
    Sum.elim_inr, Pi.add_apply, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
    Matrix.transpose_neg, Matrix.neg_mulVec, Pi.neg_apply, Function.comp_def,
    toBits, toBits_ofBits, Fin.tail_def, sub_eq_add_neg]

/-- The creator coefficient is the signed sum over deleting one occupied
coordinate. This is left exterior multiplication by `u` in increasing order. -/
theorem create_eq_sum (n : ℕ) (u : Fin n → ℝ) (x : (Fin n → Bool) → ℝ)
    (b : Fin n → Bool) :
    create n u x b = ∑ i, if b i then
      koszulSign n b i * u i * x (Function.update b i false) else 0 := by
  induction n with
  | zero => simp only [create, annihilation, Matrix.transpose_zero,
      Matrix.zero_mulVec, Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    rw [← Fin.cons_self_tail b]
    cases b 0 with
    | false =>
      rw [create_cons_false, ih, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
        koszulSign, Fin.cases_succ, Fin.tail_cons, zero_add, ← Fin.cons_update]
      rfl
    | true =>
      rw [create_cons_true, ih, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ↓reduceIte, koszulSign,
        Fin.cases_zero, Fin.cases_succ, Fin.tail_cons, one_mul,
        Fin.update_cons_zero, ← Fin.cons_update, neg_mul, sub_eq_add_neg]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases Fin.tail b i with
      | false => exact neg_zero
      | true => rfl

/-- The explicit signed deletion formula obeys the sharp creator bound for
arbitrary coefficients on every subset. -/
theorem sum_sq_signed_deletion_le (n : ℕ) (u : Fin n → ℝ)
    (x : (Fin n → Bool) → ℝ) :
    (∑ b, (∑ i, if b i then
      koszulSign n b i * u i * x (Function.update b i false) else 0) ^ 2) ≤
      (∑ i, u i ^ 2) * ∑ b, x b ^ 2 := by
  simp only [← create_eq_sum]
  exact sum_sq_create_le n u x

end LatticeProb.SubsetContraction
