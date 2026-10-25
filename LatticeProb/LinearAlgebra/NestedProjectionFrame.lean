module

/-
Nested symmetric idempotent real matrices admit compatible ordered orthonormal
frames on their original finite carrier. An orthonormal basis of the difference
range is placed before a basis of the smaller range; symmetry proves their
cross orthogonality and coordinate projection sums prove both reconstructions.
-/
public import LatticeProb.LinearAlgebra.OrthogonalFrame
public import LatticeProb.LinearAlgebra.DeterminantEndpointComparison

@[expose] public section

namespace LatticeProb.ProjectionFiltration

open scoped BigOperators InnerProductSpace Matrix
open WithLp

variable {E : Type*}

/-- Place the increment family before the old family, with total length written
as `k + m` so deletion of `m` leading columns retains the old `k` columns. -/
noncomputable def incrementFirst {m k : ℕ}
    (v : Fin m → EuclideanSpace ℝ E) (w : Fin k → EuclideanSpace ℝ E) :
    Fin (k + m) → EuclideanSpace ℝ E :=
  Fin.append v w ∘ Fin.cast (Nat.add_comm k m)

/-- The trailing columns of the increment-first family are exactly the old family. -/
theorem incrementFirst_tail {m k : ℕ}
    (v : Fin m → EuclideanSpace ℝ E) (w : Fin k → EuclideanSpace ℝ E) (j : Fin k) :
    incrementFirst v w ⟨m + j.val, by omega⟩ = w j := by
  change Fin.append v w (Fin.natAdd m j) = w j
  exact Fin.append_right v w j

/-- Cross-orthogonality makes the increment-first family orthonormal. -/
theorem orthonormal_incrementFirst [Fintype E] {m k : ℕ}
    {v : Fin m → EuclideanSpace ℝ E} {w : Fin k → EuclideanSpace ℝ E}
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (hcross : ∀ i j, inner ℝ (v i) (w j) = 0) :
    Orthonormal ℝ (incrementFirst v w) :=
  (orthonormal_append hv hw hcross).comp _ (Fin.cast_injective _)

/-- Reordering the total length does not change the sum of coordinate projections. -/
theorem projectionSum_incrementFirst [Fintype E] {m k : ℕ}
    (v : Fin m → EuclideanSpace ℝ E) (w : Fin k → EuclideanSpace ℝ E) :
    projectionSum (incrementFirst v w) Finset.univ =
      projectionSum v Finset.univ + projectionSum w Finset.univ := by
  rw [← projectionSum_append]
  simp only [projectionSum, incrementFirst, Function.comp_apply]
  exact (finCongr (Nat.add_comm k m)).sum_comp
    (fun i => rankOneProjection (Fin.append v w i))

variable [Fintype E] [DecidableEq E]

/-- **Compatible nested frames.** Every pair of nested real symmetric idempotent
matrices has an internally constructed orthonormal column frame for the larger
projection whose trailing columns reconstruct the smaller projection. The
original finite carrier is retained, including the empty-carrier case. -/
theorem exists_nested_projection_frame (P Q : Matrix E E ℝ)
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ k m : ℕ, ∃ U : Matrix E (Fin (k + m)) ℝ,
      U.transpose * U = 1 ∧
      U * U.transpose = Q ∧
      (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))) *
        (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))).transpose = P := by
  let p := P.toEuclideanLin
  let q := Q.toEuclideanLin
  have hp : p.IsSymmetricProjection := isSymmetricProjection_toEuclideanLin hPs hPi
  have hq : q.IsSymmetricProjection := isSymmetricProjection_toEuclideanLin hQs hQi
  obtain ⟨v, hv, _, hzero, hsum⟩ :=
    exists_orthonormal_increment hp hq (range_toEuclideanLin_le hle)
  let b := stdOrthonormalBasis ℝ (LinearMap.range p)
  let w := fun i => (b i : EuclideanSpace ℝ E)
  have hw : Orthonormal ℝ w :=
    b.orthonormal.comp_linearIsometry (LinearMap.range p).subtypeₗᵢ
  have hwfix (j) : p (w j) = w j :=
    (LinearMap.IsIdempotentElem.mem_range_iff hp.isIdempotentElem).mp (b j).property
  have hcross (i j) : inner ℝ (v i) (w j) = 0 := by
    rw [← hwfix j, ← hp.isSymmetric, hzero, inner_zero_left]
  have hwSum : p = projectionSum w Finset.univ := projection_eq_projectionSum hp b
  refine ⟨Module.finrank ℝ (LinearMap.range p),
    Module.finrank ℝ (LinearMap.range (q - p)), columnFrame (incrementFirst v w),
    transpose_mul_columnFrame_eq_one (orthonormal_incrementFirst hv hw hcross), ?_, ?_⟩
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_columnFrame_mul_transpose, projectionSum_incrementFirst,
      ← hsum, ← hwSum, sub_add_cancel]
  · have ht : (columnFrame (incrementFirst v w)).submatrix id
        (fun j : Fin (Module.finrank ℝ (LinearMap.range p)) =>
          (⟨Module.finrank ℝ (LinearMap.range (q - p)) + j.val, by omega⟩ :
            Fin (Module.finrank ℝ (LinearMap.range p) +
              Module.finrank ℝ (LinearMap.range (q - p))))) = columnFrame w := by
      ext e j
      exact congrArg (fun x : EuclideanSpace ℝ E => x e) (incrementFirst_tail v w j)
    rw [ht]
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_columnFrame_mul_transpose, ← hwSum]

/-- Both endpoint frames are orthonormal and reconstruct the actual nested
projections, with no frame or dimension premise supplied by the caller. -/
theorem exists_nested_orthonormal_frames (P Q : Matrix E E ℝ)
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ k m : ℕ, ∃ U : Matrix E (Fin (k + m)) ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = Q ∧
      (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))).transpose *
        U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m))) = 1 ∧
      (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))) *
        (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))).transpose = P := by
  obtain ⟨k, m, U, hU, hQ, hP⟩ := exists_nested_projection_frame P Q hPs hPi hQs hQi hle
  exact ⟨k, m, U, hU, hQ, transpose_mul_trailing_columns_eq_one U hU, hP⟩

/-- The compatible nested frame matches the ordered deletion operation used
in determinant endpoint comparison on a finite ordered ground set. -/
theorem exists_nested_projection_frame_fin {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ k m : ℕ, ∃ U : Matrix (Fin n) (Fin (k + m)) ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = Q ∧
      SubsetContraction.dropLeadingColumns U *
        (SubsetContraction.dropLeadingColumns U).transpose = P :=
  exists_nested_projection_frame P Q hPs hPi hQs hQi hle

/-- Compatible endpoint frames and their increasing-event coefficient comparison
are constructed from the actual nested projections, with no supplied frame. -/
theorem exists_nested_projection_frame_event {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.IsSymm) (hPi : P * P = P) (hQs : Q.IsSymm) (hQi : Q * Q = Q)
    (hle : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ k m : ℕ, ∃ U : Matrix (Fin n) (Fin (k + m)) ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = Q ∧
      SubsetContraction.dropLeadingColumns U *
        (SubsetContraction.dropLeadingColumns U).transpose = P ∧
      ∀ A : Set (Finset (Fin n)), (∀ S ∈ A, ∀ i, insert i S ∈ A) →
        (∑ S : Finset (Fin n), A.indicator (fun S =>
          SubsetContraction.determinantCoeff (SubsetContraction.dropLeadingColumns U) S ^ 2) S) ≤
        ∑ S : Finset (Fin n), A.indicator (fun S =>
          SubsetContraction.determinantCoeff U S ^ 2) S := by
  obtain ⟨k, m, U, hU, hQ, hP⟩ :=
    exists_nested_projection_frame_fin P Q hPs hPi hQs hQi hle
  exact ⟨k, m, U, hU, hQ, hP,
    SubsetContraction.sum_indicator_determinantCoeff_sq_dropLeadingColumns_le U hU⟩

end LatticeProb.ProjectionFiltration
