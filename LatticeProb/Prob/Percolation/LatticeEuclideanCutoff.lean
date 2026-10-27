import LatticeProb.Prob.Percolation.LatticeAnnularSup

/-! # Euclidean cutoffs on open components

A radial cutoff has finite support and controlled variation across adjacent vertices.
-/

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)

/-- A radial cutoff in the Euclidean embedding of the component. -/
def componentEuclideanCutoff (x : C) (m : {r : ℝ // 0 < r}) (y : C) : ℝ :=
  max 0 (min 1 ((2 * m.val - dist (latticeEuclideanEmbedding y.val)
    (latticeEuclideanEmbedding x.val)) / m.val))

/-- The cutoff is nonnegative. -/
theorem componentEuclideanCutoff_nonneg (x y : C) (m : {r : ℝ // 0 < r}) :
    0 ≤ componentEuclideanCutoff C x m y := le_max_left _ _

/-- The cutoff is at most one. -/
theorem componentEuclideanCutoff_le_one (x y : C) (m : {r : ℝ // 0 < r}) :
    componentEuclideanCutoff C x m y ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- The cutoff equals one inside the inner radius. -/
theorem componentEuclideanCutoff_eq_one (x y : C) (m : {r : ℝ // 0 < r})
    (h : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ≤ m.val) :
    componentEuclideanCutoff C x m y = 1 := by
  have hq : 1 ≤ (2 * m.val - dist (latticeEuclideanEmbedding y.val)
      (latticeEuclideanEmbedding x.val)) / m.val := by
    apply (le_div_iff₀ m.property).2
    linarith
  simp [componentEuclideanCutoff, min_eq_left hq]

/-- The cutoff vanishes outside the outer radius. -/
theorem componentEuclideanCutoff_eq_zero (x y : C) (m : {r : ℝ // 0 < r})
    (h : 2 * m.val ≤ dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val)) :
    componentEuclideanCutoff C x m y = 0 := by
  have hq : (2 * m.val - dist (latticeEuclideanEmbedding y.val)
      (latticeEuclideanEmbedding x.val)) / m.val ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by
      linarith) m.property.le
  simp [componentEuclideanCutoff, max_eq_left (le_trans (min_le_right _ _) hq)]

/-- The support is contained in the outer ball. -/
theorem componentEuclideanCutoff_support_subset (x : C) (m : {r : ℝ // 0 < r}) :
    Function.support (componentEuclideanCutoff C x m) ⊆
      {y : C | dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) < 2
      * m.val} := by
  intro y hy
  by_contra h
  exact hy (componentEuclideanCutoff_eq_zero C x y m (le_of_not_gt h))

/-- The cutoff has finite support. -/
theorem componentEuclideanCutoff_support (x : C) (m : {r : ℝ // 0 < r}) :
    (Function.support (componentEuclideanCutoff C x m)).Finite := by
  apply (finite_componentEuclideanBall C x.val (2 * m.val)).subset
  intro y hy
  by_contra h
  exact hy (componentEuclideanCutoff_eq_zero C x y m (le_of_not_gt h))

/-- The cutoff varies at most by distance divided by the radius. -/
theorem componentEuclideanCutoff_abs_sub_le (x y z : C) (m : {r : ℝ // 0 < r}) :
    |componentEuclideanCutoff C x m y - componentEuclideanCutoff C x m z| ≤
      dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding z.val) / m.val := by
  let a := (2 * m.val - dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding
      x.val)) / m.val
  let b := (2 * m.val - dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding
      x.val)) / m.val
  have hmax : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |min 1 a - min 1 b| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (min 1 a) (min 1 b) (0 : ℝ)
  have hmin : |min 1 a - min 1 b| ≤ |a - b| := by
    have hl : LipschitzWith 1 (fun t : ℝ => min 1 t) := LipschitzWith.id.const_min 1
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul a b
  have he : |a - b| = |dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) -
      dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)| / m.val := by
    dsimp [a, b]
    rw [show (2 * m.val - dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding
      x.val)) / m.val -
      (2 * m.val - dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding
      x.val)) / m.val =
      -(dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) -
      dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)) / m.val by ring,
      abs_div, abs_neg, abs_of_pos m.property]
  exact hmax.trans (hmin.trans (he ▸ div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _)
      m.property.le))

/-- The cutoff variation across an open edge is at most the reciprocal radius. -/
theorem componentEuclideanCutoff_adj (x y z : C) (m : {r : ℝ // 0 < r})
    (h : (openGraph ω).Adj y.val z.val) :
    |componentEuclideanCutoff C x m y - componentEuclideanCutoff C x m z| ≤ 1 / m.val := by
  simpa only [dist_embedding_adj h] using componentEuclideanCutoff_abs_sub_le C x y z m

/-- The cutoff has its prescribed values on genuine vertices of the fully open plane. -/
theorem allOpen_two_cutoff_witness :
    let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
    ∃ x y : C, x.val = 0 ∧ y.val = (2 : ℤ) • unit (0 : Fin 2) ∧
      componentEuclideanCutoff C x ⟨1, by norm_num⟩ x = 1 ∧
      componentEuclideanCutoff C x ⟨1, by norm_num⟩ y = 0 := by
  let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
  have hy : (2 : ℤ) • unit (0 : Fin 2) ∈ C.supp := by
    change (openGraph (allOpen 2)).connectedComponentMk ((2 : ℤ) • unit (0 : Fin 2)) = _
    apply SimpleGraph.ConnectedComponent.eq.mpr
    rw [openGraph_allOpen]
    exact (Graph.Zd.latticeConnected 2).preconnected _ _
  let x : C := ⟨0, rfl⟩
  let y : C := ⟨(2 : ℤ) • unit (0 : Fin 2), hy⟩
  refine ⟨x, y, rfl, rfl, ?_, ?_⟩
  · apply componentEuclideanCutoff_eq_one
    simp
  · apply componentEuclideanCutoff_eq_zero
    have h := PiLp.norm_apply_le (latticeEuclideanEmbedding y.val -
      latticeEuclideanEmbedding x.val) (0 : Fin 2)
    change |(((2 : ℤ) • unit (0 : Fin 2)) 0 : ℝ) -
      (((0 : Vertex 2) 0 : ℤ) : ℝ)| ≤ _ at h
    rw [dist_eq_norm]
    norm_num [unit, Pi.smul_apply] at h ⊢
    exact h

end
end LatticeProb.Percolation
