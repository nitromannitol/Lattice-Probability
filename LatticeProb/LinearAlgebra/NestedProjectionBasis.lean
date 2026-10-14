/-
# Orthonormal bases for increments of nested projections

The range of the difference of nested orthogonal projections has an
orthonormal basis, annihilated by the smaller projection. Summing the
coordinate projections of this basis reconstructs the difference.
-/

import LatticeProb.LinearAlgebra.OrthonormalProjectionSum



namespace LatticeProb.ProjectionFiltration

open scoped BigOperators InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Nested symmetric projections commute, with product the smaller projection. -/
theorem comp_eq_left_of_range_le {p q : V →ₗ[ℝ] V}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection)
    (hle : LinearMap.range p ≤ LinearMap.range q) : p.comp q = p := by
  have hqp := (LinearMap.IsIdempotentElem.comp_eq_right_iff hq.isIdempotentElem p).mpr hle
  ext x
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.comp_apply, ← hp.isSymmetric y (q x), ← hq.isSymmetric (p y) x]
  change inner ℝ ((q.comp p) y) x = inner ℝ y (p x)
  rw [hqp, hp.isSymmetric]

/-- The range of the difference of nested projections lies in the smaller kernel. -/
theorem range_sub_le_ker {p q : V →ₗ[ℝ] V}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection)
    (hle : LinearMap.range p ≤ LinearMap.range q) :
    LinearMap.range (q - p) ≤ LinearMap.ker p := by
  rintro x ⟨y, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub]
  have hpq := LinearMap.congr_fun (comp_eq_left_of_range_le hp hq hle) y
  have hpp := LinearMap.congr_fun hp.isIdempotentElem y
  change p (q y) = p y at hpq
  change p (p y) = p y at hpp
  change p (q y) - p (p y) = 0
  rw [hpq, hpp, sub_self]

/-- An orthonormal basis of the range reconstructs a symmetric projection
as the sum of its rank-one coordinate projections. -/
theorem projection_eq_projectionSum {d : V →ₗ[ℝ] V}
    (hd : d.IsSymmetricProjection) {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ (LinearMap.range d)) :
    d = projectionSum (fun i => (b i : V)) Finset.univ := by
  ext x
  rw [projectionSum_apply]
  have hb := congrArg ((↑) : LinearMap.range d → V)
    (b.sum_repr' ⟨d x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩)
  have hfix (i : I) : d (b i : V) = b i :=
    (LinearMap.IsIdempotentElem.mem_range_iff hd.isIdempotentElem).mp (b i).property
  have hinner (i : I) : inner ℝ (b i : V) (d x) = inner ℝ (b i : V) x := by
    rw [← hd.isSymmetric (b i : V) x, hfix]
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, hinner] using hb.symm

/-- **Orthonormal increment basis.** For any nested finite-dimensional
orthogonal projections, the difference is reconstructed by an internally
chosen orthonormal range basis, each vector killed by the smaller projection. -/
theorem exists_orthonormal_increment [FiniteDimensional ℝ V]
    {p q : V →ₗ[ℝ] V} (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection)
    (hle : LinearMap.range p ≤ LinearMap.range q) :
    ∃ v : Fin (Module.finrank ℝ (LinearMap.range (q - p))) → V,
      Orthonormal ℝ v ∧
      (∀ i, v i ∈ LinearMap.range (q - p)) ∧
      (∀ i, p (v i) = 0) ∧
      q - p = projectionSum v Finset.univ := by
  let b := stdOrthonormalBasis ℝ (LinearMap.range (q - p))
  refine ⟨fun i => (b i : V), ?_, fun i => (b i).property, ?_, ?_⟩
  · exact b.orthonormal.comp_linearIsometry (LinearMap.range (q - p)).subtypeₗᵢ
  · intro i
    exact LinearMap.mem_ker.mp (range_sub_le_ker hp hq hle (b i).property)
  · exact projection_eq_projectionSum (hp.sub_of_range_le_range hq hle) b

end LatticeProb.ProjectionFiltration
