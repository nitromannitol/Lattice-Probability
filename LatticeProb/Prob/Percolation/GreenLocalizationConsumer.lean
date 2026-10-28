import LatticeProb.Prob.Percolation.GreenLocalizationGeometry
import LatticeProb.Prob.Percolation.GreenColumnHarmonic

/-! # Examples of localization on the open plane -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace LatticeProb.Percolation

noncomputable section

/-- The working regime is inhabited by two explicit vertices of the fully open plane. -/
theorem allOpen_localization_witness :
    let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
    ∃ x y : C, x.val = 0 ∧ y.val = (10000 : ℤ) • unit (0 : Fin 2) ∧
      max (max 64 (2 : ℝ)) (2 * 0) <
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) ^ (1 / 2 : ℝ) ∧
      4096 < dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) ∧
      ∀ (j : Fin 2) (v : C),
        v ∈ componentEuclideanBall C x.val
          (dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) / 4) →
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) / 2 <
          dist (latticeEuclideanEmbedding v.val) (latticeEuclideanEmbedding (y.val + unit j)) := by
  let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
  have hy : (10000 : ℤ) • unit (0 : Fin 2) ∈ C.supp := by
    change (openGraph (allOpen 2)).connectedComponentMk ((10000 : ℤ) • unit (0 : Fin 2)) = _
    apply SimpleGraph.ConnectedComponent.eq.mpr
    rw [openGraph_allOpen]
    exact (Graph.Zd.latticeConnected 2).preconnected _ _
  let x : C := ⟨0, rfl⟩
  let y : C := ⟨(10000 : ℤ) • unit (0 : Fin 2), hy⟩
  have hdist : (10000 : ℝ) ≤
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) := by
    rw [dist_comm, dist_eq_norm]
    have h := PiLp.norm_apply_le (latticeEuclideanEmbedding y.val -
      latticeEuclideanEmbedding x.val) (0 : Fin 2)
    change |(((10000 : ℤ) • unit (0 : Fin 2)) 0 : ℝ) -
      (((0 : Vertex 2) 0 : ℤ) : ℝ)| ≤ _ at h
    norm_num [unit, Pi.smul_apply] at h ⊢
    exact h
  have hs : (100 : ℝ) ≤ Real.sqrt
      (dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val)) := by
    have h := Real.sqrt_le_sqrt hdist
    norm_num at h
    exact h
  have hwork : max (max 64 (2 : ℝ)) (2 * 0) <
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
    linarith
  have hb := localization_scale_bounds (dist_nonneg :
    0 ≤ dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val))
    (by norm_num : (0 : ℝ) < 1 / 2) (le_refl _) hwork
  refine ⟨x, y, rfl, rfl, hwork, hb.1, ?_⟩
  intro j v hv
  exact (localization_ball_separation C x.val y.val j v hb.1 hv).2

/-- Two legitimate columns are harmonic after subtraction on the separated ball. -/
theorem separated_green_columns_harmonic {d : ℕ} (hd : 2 ≤ d) {ω : Configuration d}
    (C : OpenComponent ω) (x y : Vertex d) (j : Fin d) (p q : C)
    (hp : p.val = y) (hq : q.val = y + unit j) (g h : C → ℝ) (c T : ℝ)
    (hg : IsGreenColumn d hd C p g) (hh : IsGreenColumn d hd C q h)
    (hD : 4096 < dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y))
    (hT : T < dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 128) :
    ∀ v ∈ componentEuclideanBall C x
      (dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) / 4),
      componentLaplacian C (fun z => g z - h z - c) v = 0 := by
  obtain ⟨hp', hq', _⟩ := localization_poles_and_threshold C x y j p q hp hq T hD hT
  exact greenColumn_sub_sub_const_harmonic hd C p q g h c hg hh x _ hp' hq'

end
end LatticeProb.Percolation
