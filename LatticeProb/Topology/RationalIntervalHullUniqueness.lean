import LatticeProb.Topology.PlanarFilledHull

/-! # Reconstruction from filled interval images -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- A continuous planar curve is determined by the filled hulls of its images
on all nondegenerate intervals with rational endpoints. -/
theorem Continuous.eq_of_rational_interval_planarFilledHull_eq
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q r : ℚ, q < r →
      planarFilledHull (f '' Icc (q : ℝ) (r : ℝ)) =
        planarFilledHull (g '' Icc (q : ℝ) (r : ℝ))) : f = g := by
  apply Continuous.ext_on (Rat.denseRange_cast : Dense (range ((↑) : ℚ → ℝ))) hf hg
  rintro _ ⟨q, rfl⟩
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp (hg.continuousAt) ε hε
  obtain ⟨r, hqr, hrδ⟩ := exists_rat_btwn (lt_add_of_pos_right (q : ℝ) hδ)
  have hqr' : q < r := by exact_mod_cast hqr
  have hsub : g '' Icc (q : ℝ) (r : ℝ) ⊆ ball (g q) ε := by
    rintro _ ⟨t, ht, rfl⟩
    apply hcont
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hhull := planarFilledHull_subset_convex (convex_ball (g q) ε)
    (nonempty_ball.mpr hε) hsub
  have hmem : f q ∈ planarFilledHull (f '' Icc (q : ℝ) (r : ℝ)) :=
    Or.inl ⟨(q : ℝ), ⟨le_rfl, hqr.le⟩, rfl⟩
  rw [h q r hqr'] at hmem
  exact (hhull hmem).le

end LatticeProb
