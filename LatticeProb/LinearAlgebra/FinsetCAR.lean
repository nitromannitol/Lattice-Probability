/-
# Canonical anticommutation on ordinary finite subsets

The literal signed sums are transported from the recursive subset matrices.
-/

import LatticeProb.LinearAlgebra.FiniteSubsetContraction



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical Matrix
noncomputable section

/-- Signed contraction of ordinary finset coefficients. -/
def finsetContract {n : ℕ} (u : Fin n → ℝ) (x : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n, if i ∈ S then 0 else insertionSign S i * u i * x (insert i S)

/-- Signed left creation of ordinary finset coefficients. -/
def finsetCreate {n : ℕ} (u : Fin n → ℝ) (x : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ i : Fin n, if i ∈ S then insertionSign S i * u i * x (S.erase i) else 0

/-- Finset contraction is the actual CAR annihilator under occupation bits. -/
theorem finsetContract_bits {n : ℕ} (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) (b : Fin n → Bool) :
    finsetContract u x (bitsFinsetEquiv n b) =
      contract n u (fun t => x (bitsFinsetEquiv n t)) b := by
  rw [contract_eq_sum]
  simp only [finsetContract, koszulSign_eq_insertionSign, bitsFinsetEquiv_update,
    ← mem_bitsFinsetEquiv]

/-- Finset creation is the actual CAR creator under occupation bits. -/
theorem finsetCreate_bits {n : ℕ} (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) (b : Fin n → Bool) :
    finsetCreate u x (bitsFinsetEquiv n b) =
      create n u (fun t => x (bitsFinsetEquiv n t)) b := by
  rw [create_eq_sum]
  simp only [finsetCreate, koszulSign_eq_insertionSign, bitsFinsetEquiv_update_false,
    ← mem_bitsFinsetEquiv]

/-- The CAR identity evaluated on an arbitrary Bool-subset vector. -/
theorem contract_create_add_create_contract (n : ℕ) (u : Fin n → ℝ)
    (x : (Fin n → Bool) → ℝ) (b : Fin n → Bool) :
    contract n u (create n u x) b + create n u (contract n u x) b =
      (∑ i, u i ^ 2) * x b := by
  have h := congrArg (fun M : Matrix (SubsetIndex n) (SubsetIndex n) ℝ =>
    (M *ᵥ (fun s => x (toBits n s))) (ofBits n b)) (annihilation_car n u)
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, toBits_ofBits,
    contract, create, ofBits_toBits] using h

/-- **Finset CAR.** Literal creation and contraction anticommute to squared
length times the identity, with the exact increasing-order insertion signs. -/
theorem finsetContract_create_add_create_contract {n : ℕ} (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    finsetContract u (finsetCreate u x) S + finsetCreate u (finsetContract u x) S =
      (∑ i, u i ^ 2) * x S := by
  obtain ⟨b, rfl⟩ := (bitsFinsetEquiv n).surjective S
  rw [finsetContract_bits, finsetCreate_bits]
  simpa only [finsetCreate_bits, finsetContract_bits] using
    contract_create_add_create_contract n u (fun t => x (bitsFinsetEquiv n t)) b

/-- Contraction is zero on the zero coefficient vector. -/
theorem finsetContract_zero {n : ℕ} (u : Fin n → ℝ) :
    finsetContract u (fun _ => 0) = 0 := by
  funext S
  simp only [finsetContract, mul_zero, ite_self, Finset.sum_const_zero, Pi.zero_apply]

/-- Creation is zero on the zero coefficient vector. -/
theorem finsetCreate_zero {n : ℕ} (u : Fin n → ℝ) :
    finsetCreate u (fun _ => 0) = 0 := by
  funext S
  simp only [finsetCreate, mul_zero, ite_self, Finset.sum_const_zero, Pi.zero_apply]

end
end LatticeProb.SubsetContraction
