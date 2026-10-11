/-
# Sums of orthonormal coordinate projections

Finite sums of projections onto an orthonormal family are orthogonal
projections. Adding such a sum to a projection that annihilates the family
again gives an orthogonal projection.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Symmetric



namespace LatticeProb.ProjectionFiltration

open scoped BigOperators InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {I : Type*}

/-- The orthogonal rank-one operator `x ↦ ⟪v,x⟫ v`. -/
noncomputable def rankOneProjection (v : V) : V →ₗ[ℝ] V :=
  (InnerProductSpace.rankOne ℝ v v).toLinearMap

/-- The sum of the coordinate projections indexed by a finite set. -/
noncomputable def projectionSum (v : I → V) (s : Finset I) : V →ₗ[ℝ] V :=
  ∑ i ∈ s, rankOneProjection (v i)

/-- Evaluation of a sum of coordinate projections. -/
theorem projectionSum_apply (v : I → V) (s : Finset I) (x : V) :
    projectionSum v s x = ∑ i ∈ s, inner ℝ (v i) x • v i := by
  simp only [projectionSum, LinearMap.sum_apply, rankOneProjection,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]

/-- A coordinate projection sum fixes every included member of the family. -/
theorem projectionSum_apply_of_mem [DecidableEq I] {v : I → V} (hv : Orthonormal ℝ v)
    {s : Finset I} {i : I} (hi : i ∈ s) : projectionSum v s (v i) = v i := by
  rw [projectionSum_apply]
  simp only [orthonormal_iff_ite.mp hv, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', if_pos hi]

/-- A coordinate projection sum kills every omitted member of the family. -/
theorem projectionSum_apply_of_not_mem [DecidableEq I] {v : I → V} (hv : Orthonormal ℝ v)
    {s : Finset I} {i : I} (hi : i ∉ s) : projectionSum v s (v i) = 0 := by
  rw [projectionSum_apply]
  simp only [orthonormal_iff_ite.mp hv, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', if_neg hi]

/-- **Orthonormal projection sum.** Every finite coordinate projection sum of an orthonormal family is an
orthogonal projection. -/
theorem projectionSum_isSymmetricProjection [DecidableEq I] {v : I → V} (hv : Orthonormal ℝ v)
    (s : Finset I) : (projectionSum v s).IsSymmetricProjection := by
  refine ⟨?_, LinearMap.isSymmetric_sum s (fun i _ =>
    InnerProductSpace.isSymmetric_rankOne_self (v i))⟩
  apply LinearMap.ext
  intro x
  change projectionSum v s (projectionSum v s x) = projectionSum v s x
  nth_rw 2 [projectionSum_apply]
  rw [map_sum, projectionSum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, projectionSum_apply_of_mem hv hi]

/-- A symmetric projection annihilating an orthonormal family remains an
orthogonal projection after adding any finite coordinate projection sum. -/
theorem add_projectionSum_isSymmetricProjection [DecidableEq I] {p : V →ₗ[ℝ] V}
    (hp : p.IsSymmetricProjection) {v : I → V} (hv : Orthonormal ℝ v)
    (hzero : ∀ i, p (v i) = 0) (s : Finset I) :
    (p + projectionSum v s).IsSymmetricProjection := by
  have hs := projectionSum_isSymmetricProjection hv s
  have hps : p * projectionSum v s = 0 := by
    ext x
    change p (projectionSum v s x) = 0
    rw [projectionSum_apply, map_sum]
    simp only [map_smul, hzero, smul_zero, Finset.sum_const_zero]
  have hsp : projectionSum v s * p = 0 := by
    ext x
    change projectionSum v s (p x) = 0
    rw [projectionSum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hp.isSymmetric (v i) x, hzero, inner_zero_left, zero_smul]
  exact ⟨hp.isIdempotentElem.add hs.isIdempotentElem (by rw [hps, hsp, add_zero]),
    hp.isSymmetric.add hs.isSymmetric⟩

/-- Inclusion of coordinate sets gives inclusion of the augmented projection ranges. -/
theorem range_add_projectionSum_mono [DecidableEq I] {p : V →ₗ[ℝ] V}
    (hp : p.IsSymmetricProjection) {v : I → V} (hv : Orthonormal ℝ v)
    (hzero : ∀ i, p (v i) = 0) {s t : Finset I} (hst : s ⊆ t) :
    LinearMap.range (p + projectionSum v s) ≤ LinearMap.range (p + projectionSum v t) := by
  have ht := add_projectionSum_isSymmetricProjection hp hv hzero t
  have hpx (x : V) : (p + projectionSum v t) (p x) = p x := by
    rw [LinearMap.add_apply]
    have hpp := LinearMap.congr_fun hp.isIdempotentElem x
    change p (p x) = p x at hpp
    rw [hpp, projectionSum_apply]
    have hz : (∑ i ∈ t, inner ℝ (v i) (p x) • v i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← hp.isSymmetric (v i) x, hzero, inner_zero_left, zero_smul]
    rw [hz, add_zero]
  rintro y ⟨x, rfl⟩
  rw [LinearMap.IsIdempotentElem.mem_range_iff ht.isIdempotentElem]
  change (p + projectionSum v t) (p x + projectionSum v s x) =
    p x + projectionSum v s x
  rw [map_add, hpx, projectionSum_apply, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, LinearMap.add_apply, hzero, projectionSum_apply_of_mem hv (hst hi), zero_add]

/-- Indices of the first `k` members of a family indexed by `Fin n`. -/
def initialSegment (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

/-- The initial segment of length zero is empty. -/
theorem initialSegment_zero (n : ℕ) : initialSegment n 0 = ∅ := by
  simp only [initialSegment, Nat.not_lt_zero, Finset.filter_false]

/-- The initial segment of full length includes every index. -/
theorem initialSegment_self (n : ℕ) : initialSegment n n = Finset.univ := by
  apply Finset.filter_true_of_mem
  intro i _
  exact i.isLt

/-- Consecutive initial segments differ by exactly the next index. -/
theorem initialSegment_succ {n : ℕ} (i : Fin n) :
    initialSegment n (i.val + 1) = insert i (initialSegment n i.val) := by
  ext j
  simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  omega

/-- The next index does not occur in the preceding initial segment. -/
theorem not_mem_initialSegment {n : ℕ} (i : Fin n) : i ∉ initialSegment n i.val := by
  simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and, lt_self_iff_false,
    not_false_eq_true]

/-- Initial segments increase with their length. -/
theorem initialSegment_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    initialSegment n k ⊆ initialSegment n l := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hkl⟩

/-- The next partial sum adds exactly one rank-one coordinate projection. -/
theorem projectionSum_initialSegment_succ {n : ℕ} (v : Fin n → V) (i : Fin n) :
    projectionSum v (initialSegment n (i.val + 1)) =
      projectionSum v (initialSegment n i.val) + rankOneProjection (v i) := by
  rw [initialSegment_succ]
  simp only [projectionSum, Finset.sum_insert (not_mem_initialSegment i), add_comm]

/-- The range of the coordinate projection of a unit vector is its one-dimensional span. -/
theorem range_rankOneProjection {v : V} (hv : ‖v‖ = 1) :
    LinearMap.range (rankOneProjection v) = Submodule.span ℝ {v} := by
  have hfix : rankOneProjection v v = v := by
    simp only [rankOneProjection, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_self_eq_norm_sq, hv, one_pow, one_smul]
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨inner ℝ v y, rfl⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a • v, by rw [map_smul, hfix]⟩

/-- The coordinate projection of a unit vector has range dimension one. -/
theorem finrank_range_rankOneProjection {v : V} (hv : ‖v‖ = 1) :
    Module.finrank ℝ (LinearMap.range (rankOneProjection v)) = 1 := by
  rw [range_rankOneProjection hv]
  apply finrank_span_singleton
  intro h
  rw [h, norm_zero] at hv
  exact zero_ne_one hv

/-- An orthonormal family's full coordinate sum has range equal to its span. -/
theorem range_projectionSum_univ {I : Type*} [Fintype I] [DecidableEq I]
    {v : I → V} (hv : Orthonormal ℝ v) :
    LinearMap.range (projectionSum v Finset.univ) = Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    rw [projectionSum_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact ⟨v i, projectionSum_apply_of_mem hv (Finset.mem_univ i)⟩

end LatticeProb.ProjectionFiltration
