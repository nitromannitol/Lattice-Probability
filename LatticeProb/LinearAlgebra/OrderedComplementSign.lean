module

/-
# Signs of increasing complementary orders

List a finite vertex set by its increasing complement followed by its
increasing roots. The relative sign of two such full orders is the parity
of the sum of the two root-label sums. Ordered unit-column determinant
expansion proves the sign without counting inversions explicitly.
-/
public import LatticeProb.LinearAlgebra.InverseComplementaryMinor
public import LatticeProb.LinearAlgebra.Matrix.RootColumnExpansion

@[expose] public section



namespace LatticeProb.LinearAlgebra

open Matrix
open scoped BigOperators

/-- The increasing complement followed by the increasing root set is a full
order of the original finite carrier. -/
noncomputable def increasingComplementRootEquiv {α : Type*} [Fintype α]
    [LinearOrder α] {d k : ℕ} (I : Finset α) (hI : I.card = k) (hC : Iᶜ.card = d) :
    (Fin d ⊕ Fin k) ≃ α :=
  Equiv.ofBijective
    (Sum.elim (Iᶜ.orderEmbOfFin hC) (I.orderEmbOfFin hI)) (by
      constructor
      · intro x y h
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg Sum.inl ((Iᶜ.orderEmbOfFin hC).injective h)
        · have hx := Iᶜ.orderEmbOfFin_mem hC x
          have hy := I.orderEmbOfFin_mem hI y
          change Iᶜ.orderEmbOfFin hC x = I.orderEmbOfFin hI y at h
          exact False.elim ((Finset.mem_compl.mp hx) (h.symm ▸ hy))
        · have hx := I.orderEmbOfFin_mem hI x
          have hy := Iᶜ.orderEmbOfFin_mem hC y
          change I.orderEmbOfFin hI x = Iᶜ.orderEmbOfFin hC y at h
          exact False.elim ((Finset.mem_compl.mp hy) (h ▸ hx))
        · exact congrArg Sum.inr ((I.orderEmbOfFin hI).injective h)
      · intro x
        by_cases hx : x ∈ I
        · refine ⟨Sum.inr ((I.orderIsoOfFin hI).symm ⟨x, hx⟩), ?_⟩
          exact congrArg Subtype.val ((I.orderIsoOfFin hI).apply_symm_apply ⟨x, hx⟩)
        · refine ⟨Sum.inl ((Iᶜ.orderIsoOfFin hC).symm
            ⟨x, Finset.mem_compl.mpr hx⟩), ?_⟩
          exact congrArg Subtype.val ((Iᶜ.orderIsoOfFin hC).apply_symm_apply
            ⟨x, Finset.mem_compl.mpr hx⟩))

/-- The initial part of the full order is the increasing complement. -/
theorem increasingComplementRootEquiv_inl {α : Type*} [Fintype α] [LinearOrder α]
    {d k : ℕ} (I : Finset α) (hI : I.card = k) (hC : Iᶜ.card = d) (i : Fin d) :
    increasingComplementRootEquiv I hI hC (Sum.inl i) = Iᶜ.orderEmbOfFin hC i := rfl

/-- The final part of the full order is the increasing root list. -/
theorem increasingComplementRootEquiv_inr {α : Type*} [Fintype α] [LinearOrder α]
    {d k : ℕ} (I : Finset α) (hI : I.card = k) (hC : Iᶜ.card = d) (i : Fin k) :
    increasingComplementRootEquiv I hI hC (Sum.inr i) = I.orderEmbOfFin hI i := rfl

/-- The sign of the increasing complement followed by roots equals the
root-label parity plus the label sum of the final block positions. -/
theorem sign_increasingComplementRootEquiv {d k : ℕ}
    (I : Finset (Fin (d + k))) (hI : I.card = k) (hC : Iᶜ.card = d) :
    (Equiv.Perm.sign (finSumFinEquiv.symm.trans
      (increasingComplementRootEquiv I hI hC)) : ℤ) =
      (-1 : ℤ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ r : Fin k, (d + (r : ℕ)))) := by
  let p : Equiv.Perm (Fin (d + k)) :=
    finSumFinEquiv.symm.trans (increasingComplementRootEquiv I hI hC)
  let A : Matrix (Fin (d + k)) (Fin d) ℤ :=
    (1 : Matrix (Fin (d + k)) (Fin (d + k)) ℤ).submatrix id (Iᶜ.orderEmbOfFin hC)
  have hp : (1 : Matrix (Fin (d + k)) (Fin (d + k)) ℤ).submatrix id p =
      Matrix.appendRootColumns A I hI := by
    ext x j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Matrix.appendRootColumns_castAdd]
      change (1 : Matrix (Fin (d + k)) (Fin (d + k)) ℤ) x
        (increasingComplementRootEquiv I hI hC (finSumFinEquiv.symm (Fin.castAdd k i))) =
        (1 : Matrix (Fin (d + k)) (Fin (d + k)) ℤ) x (Iᶜ.orderEmbOfFin hC i)
      rw [finSumFinEquiv_symm_apply_castAdd, increasingComplementRootEquiv_inl]
    · simp only [Matrix.submatrix_apply, id_eq, p, Equiv.trans_apply,
        finSumFinEquiv_symm_apply_natAdd, increasingComplementRootEquiv_inr,
        Matrix.appendRootColumns_natAdd, Matrix.one_apply]
  have hA : A.submatrix (Iᶜ.orderEmbOfFin hC) id = 1 := by
    ext i j
    simp only [A, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      (Iᶜ.orderEmbOfFin hC).injective.eq_iff]
  have hd := Matrix.det_appendRootColumns A I hI
  rw [← hp, Matrix.det_permute', Matrix.det_one, mul_one, hA, Matrix.det_one,
    mul_one] at hd
  exact hd

/-- **Root-label parity of independent increasing orders.** The relative
sign of the increasing complement/root orders is `(-1)` to the sum of the
two root-label sums. The equal terminal-block position parities cancel. -/
theorem sign_increasingComplementRootEquiv_trans_symm {d k : ℕ}
    (I J : Finset (Fin (d + k))) (hI : I.card = k) (hJ : J.card = k)
    (hCI : Iᶜ.card = d) (hCJ : Jᶜ.card = d) :
    (Equiv.Perm.sign ((increasingComplementRootEquiv J hJ hCJ).trans
      (increasingComplementRootEquiv I hI hCI).symm) : ℤ) =
      (-1 : ℤ) ^ ((∑ x ∈ I, (x : ℕ)) + (∑ y ∈ J, (y : ℕ))) := by
  let e := increasingComplementRootEquiv I hI hCI
  let f := increasingComplementRootEquiv J hJ hCJ
  let p : Equiv.Perm (Fin (d + k)) := finSumFinEquiv.symm.trans e
  let q : Equiv.Perm (Fin (d + k)) := finSumFinEquiv.symm.trans f
  have hs : Equiv.Perm.sign (f.trans e.symm) = Equiv.Perm.sign (q.trans p.symm) := by
    apply Equiv.Perm.sign_eq_sign_of_equiv _ _ finSumFinEquiv
    intro x
    simp only [p, q, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.symm_symm]
  rw [hs, Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, Units.val_mul,
    sign_increasingComplementRootEquiv I hI hCI,
    sign_increasingComplementRootEquiv J hJ hCJ, pow_add, pow_add]
  have hsq : (-1 : ℤ) ^ (∑ r : Fin k, (d + (r : ℕ))) *
      (-1 : ℤ) ^ (∑ r : Fin k, (d + (r : ℕ))) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  calc
    _ = ((-1 : ℤ) ^ (∑ x ∈ I, (x : ℕ)) * (-1 : ℤ) ^ (∑ y ∈ J, (y : ℕ))) *
        ((-1 : ℤ) ^ (∑ r : Fin k, (d + (r : ℕ))) *
          (-1 : ℤ) ^ (∑ r : Fin k, (d + (r : ℕ)))) := by ring
    _ = _ := by rw [hsq, mul_one, ← pow_add]

end LatticeProb.LinearAlgebra
