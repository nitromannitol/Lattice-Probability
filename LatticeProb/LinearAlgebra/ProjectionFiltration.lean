module

/-
# Finite filtrations of nested orthogonal projections

Nested real symmetric idempotent matrices admit a filtration by orthogonal
rank-one increments. The Euclidean operator representation supplies an
orthonormal basis of the range of their difference.
-/

public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import LatticeProb.LinearAlgebra.NestedProjectionBasis

@[expose] public section



namespace LatticeProb.ProjectionFiltration

open scoped BigOperators InnerProductSpace Matrix
open WithLp

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Inclusion of the ordinary matrix ranges transports to Euclidean space. -/
theorem range_toEuclideanLin_le {P Q : Matrix E E ℝ}
    (h : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    LinearMap.range P.toEuclideanLin ≤ LinearMap.range Q.toEuclideanLin := by
  rintro x ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := h (LinearMap.mem_range.mpr ⟨ofLp y, rfl⟩)
  exact ⟨toLp 2 z, congrArg (toLp 2) hz⟩

/-- Euclidean range inclusion transports back to the ordinary matrix carrier. -/
theorem range_mulVecLin_le {P Q : Matrix E E ℝ}
    (h : LinearMap.range P.toEuclideanLin ≤ LinearMap.range Q.toEuclideanLin) :
    LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin := by
  rintro x ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := h (LinearMap.mem_range.mpr ⟨toLp 2 y, rfl⟩)
  exact ⟨ofLp z, congrArg ofLp hz⟩

/-- A real symmetric idempotent matrix acts as an orthogonal projection. -/
theorem isSymmetricProjection_toEuclideanLin {P : Matrix E E ℝ}
    (hs : P.IsSymm) (hi : P * P = P) : P.toEuclideanLin.IsSymmetricProjection := by
  refine ⟨?_, Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_⟩
  · change P.toEuclideanLin.comp P.toEuclideanLin = P.toEuclideanLin
    rw [← Matrix.toLpLin_mul_same, hi]
  · exact Matrix.isHermitian_iff_isSymm.mpr hs

/-- The difference of nested real symmetric projections is an orthogonal projection. -/
theorem difference_isSymmetricProjection {P Q : Matrix E E ℝ}
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    (Q - P).toEuclideanLin.IsSymmetricProjection := by
  rw [map_sub]
  exact (isSymmetricProjection_toEuclideanLin hPs hPi).sub_of_range_le_range
    (isSymmetricProjection_toEuclideanLin hQs hQi) (range_toEuclideanLin_le hle)

/-- The matrix of an orthogonal projection is symmetric and idempotent. -/
theorem isSymm_and_mul_self {P : Matrix E E ℝ}
    (h : P.toEuclideanLin.IsSymmetricProjection) : P.IsSymm ∧ P * P = P := by
  refine ⟨Matrix.isHermitian_iff_isSymm.mp
    (Matrix.isSymmetric_toEuclideanLin_iff.mp h.isSymmetric), ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same]
  exact h.isIdempotentElem

/-- The actual matrix difference of nested projections is symmetric and idempotent. -/
theorem difference_isSymm_and_mul_self {P Q : Matrix E E ℝ}
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    (Q - P).IsSymm ∧ (Q - P) * (Q - P) = Q - P :=
  isSymm_and_mul_self (difference_isSymmetricProjection hPs hPi hQs hQi hle)

/-- The partial-sum matrix obtained by augmenting `P` with the first `k`
coordinate projections of a Euclidean vector family. -/
noncomputable def filtrationMatrix {n : ℕ} (P : Matrix E E ℝ)
    (v : Fin n → EuclideanSpace ℝ E) (k : ℕ) : Matrix E E ℝ :=
  Matrix.toEuclideanLin.symm
    (P.toEuclideanLin + projectionSum v (initialSegment n k))

/-- The Euclidean operator represented by the partial-sum matrix. -/
theorem toEuclideanLin_filtrationMatrix {n : ℕ} (P : Matrix E E ℝ)
    (v : Fin n → EuclideanSpace ℝ E) (k : ℕ) :
    (filtrationMatrix P v k).toEuclideanLin =
      P.toEuclideanLin + projectionSum v (initialSegment n k) :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- The partial-sum matrix is literally the base plus a sum of coordinate outer products. -/
theorem filtrationMatrix_eq_sum {n : ℕ} (P : Matrix E E ℝ)
    (v : Fin n → EuclideanSpace ℝ E) (k : ℕ) :
    filtrationMatrix P v k = P + ∑ i ∈ initialSegment n k,
      Matrix.vecMulVec (ofLp (v i)) (ofLp (v i)) := by
  simp only [filtrationMatrix, projectionSum, map_add, LinearEquiv.symm_apply_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (InnerProductSpace.symm_toEuclideanLin_rankOne (v i) (v i)).trans
    (by simp only [star_trivial])

/-- The filtration begins at its base projection. -/
theorem filtrationMatrix_zero {n : ℕ} (P : Matrix E E ℝ)
    (v : Fin n → EuclideanSpace ℝ E) : filtrationMatrix P v 0 = P := by
  simp only [filtrationMatrix, initialSegment_zero, projectionSum, Finset.sum_empty,
    add_zero, LinearEquiv.symm_apply_apply]

/-- Every consecutive partial-sum matrix adds the next rank-one coordinate matrix. -/
theorem filtrationMatrix_succ {n : ℕ} (P : Matrix E E ℝ)
    (v : Fin n → EuclideanSpace ℝ E) (i : Fin n) :
    filtrationMatrix P v (i.val + 1) = filtrationMatrix P v i.val +
      Matrix.vecMulVec (ofLp (v i)) (ofLp (v i)) := by
  simp only [filtrationMatrix, projectionSum_initialSegment_succ, ← add_assoc, map_add]
  congr 1
  exact (InnerProductSpace.symm_toEuclideanLin_rankOne (v i) (v i)).trans
    (by simp only [star_trivial])

/-- A partial-sum matrix of an orthonormal family annihilated by the base
projection is itself symmetric and idempotent. -/
theorem filtrationMatrix_isSymm_and_mul_self {n : ℕ} {P : Matrix E E ℝ}
    (hPs : P.IsSymm) (hPi : P * P = P) {v : Fin n → EuclideanSpace ℝ E}
    (hv : Orthonormal ℝ v) (hzero : ∀ i, P.toEuclideanLin (v i) = 0) (k : ℕ) :
    (filtrationMatrix P v k).IsSymm ∧
      filtrationMatrix P v k * filtrationMatrix P v k = filtrationMatrix P v k := by
  apply isSymm_and_mul_self
  rw [toEuclideanLin_filtrationMatrix]
  exact add_projectionSum_isSymmetricProjection
    (isSymmetricProjection_toEuclideanLin hPs hPi) hv hzero _

/-- The ordinary matrix ranges increase along the filtration. -/
theorem range_filtrationMatrix_mono {n : ℕ} {P : Matrix E E ℝ}
    (hPs : P.IsSymm) (hPi : P * P = P) {v : Fin n → EuclideanSpace ℝ E}
    (hv : Orthonormal ℝ v) (hzero : ∀ i, P.toEuclideanLin (v i) = 0)
    {k l : ℕ} (hkl : k ≤ l) :
    LinearMap.range (filtrationMatrix P v k).mulVecLin ≤
      LinearMap.range (filtrationMatrix P v l).mulVecLin := by
  apply range_mulVecLin_le
  rw [toEuclideanLin_filtrationMatrix, toEuclideanLin_filtrationMatrix]
  exact range_add_projectionSum_mono (isSymmetricProjection_toEuclideanLin hPs hPi)
    hv hzero (initialSegment_mono n hkl)

/-- The next unit vector is orthogonal to the current matrix range. -/
theorem filtrationMatrix_mulVec_next_eq_zero {n : ℕ} {P : Matrix E E ℝ}
    {v : Fin n → EuclideanSpace ℝ E} (hv : Orthonormal ℝ v)
    (hzero : ∀ i, P.toEuclideanLin (v i) = 0) (i : Fin n) :
    filtrationMatrix P v i.val *ᵥ ofLp (v i) = 0 := by
  have h : (filtrationMatrix P v i.val).toEuclideanLin (v i) = 0 := by
    rw [toEuclideanLin_filtrationMatrix, LinearMap.add_apply, hzero,
      projectionSum_apply_of_not_mem hv (not_mem_initialSegment i), add_zero]
  exact congrArg ofLp h

/-- **Finite rank filtration.** Nested symmetric idempotent real matrices
admit an orthonormal difference-range family and a finite chain of partial
rank-one sums from the smaller matrix to the larger matrix. No basis or
chain hypothesis is required. -/
theorem exists_rank_filtration {P Q : Matrix E E ℝ}
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ v : Fin (Module.finrank ℝ (LinearMap.range (Q - P).toEuclideanLin)) →
        EuclideanSpace ℝ E,
      Orthonormal ℝ v ∧
      (∀ i, v i ∈ LinearMap.range (Q - P).toEuclideanLin) ∧
      filtrationMatrix P v 0 = P ∧
      filtrationMatrix P v (Module.finrank ℝ (LinearMap.range (Q - P).toEuclideanLin)) = Q ∧
      (∀ k, (filtrationMatrix P v k).IsSymm ∧
        filtrationMatrix P v k * filtrationMatrix P v k = filtrationMatrix P v k) ∧
      (∀ k l, k ≤ l → LinearMap.range (filtrationMatrix P v k).mulVecLin ≤
        LinearMap.range (filtrationMatrix P v l).mulVecLin) ∧
      (∀ i, filtrationMatrix P v (i.val + 1) = filtrationMatrix P v i.val +
        Matrix.vecMulVec (ofLp (v i)) (ofLp (v i)) ∧
        filtrationMatrix P v i.val *ᵥ ofLp (v i) = 0) := by
  have hp := isSymmetricProjection_toEuclideanLin hPs hPi
  have hq := isSymmetricProjection_toEuclideanLin hQs hQi
  have hex := exists_orthonormal_increment hp hq (range_toEuclideanLin_le hle)
  have hdiff : (Q - P).toEuclideanLin = Q.toEuclideanLin - P.toEuclideanLin :=
    map_sub Matrix.toEuclideanLin Q P
  rw [← hdiff] at hex
  obtain ⟨v, hv, hmem, hzero, hsum⟩ := hex
  refine ⟨v, hv, hmem, filtrationMatrix_zero P v, ?_,
    filtrationMatrix_isSymm_and_mul_self hPs hPi hv hzero,
    fun _ _ hkl => range_filtrationMatrix_mono hPs hPi hv hzero hkl,
    fun i => ⟨filtrationMatrix_succ P v i,
      filtrationMatrix_mulVec_next_eq_zero hv hzero i⟩⟩
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_filtrationMatrix, initialSegment_self, ← hsum, map_sub, add_sub_cancel]

end LatticeProb.ProjectionFiltration
