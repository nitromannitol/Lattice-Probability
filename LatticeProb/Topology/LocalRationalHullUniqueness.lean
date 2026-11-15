import LatticeProb.Topology.PlanarFilledHull

/-! # Local reconstruction from filled interval images -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- A continuous planar curve segment is determined by the filled hulls of its
images on rational subintervals strictly inside the segment. -/
theorem Continuous.eqOn_of_rational_interval_planarFilledHull_eq
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a < b)
    (h : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < b →
      planarFilledHull (f '' Icc (p : ℝ) (q : ℝ)) =
        planarFilledHull (g '' Icc (p : ℝ) (q : ℝ))) : EqOn f g (Icc a b) := by
  have hinterior : Ioo a b ⊆ {t | f t = g t} := by
    intro t ht
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hg.continuousAt ε hε
    obtain ⟨p, hap, hpt⟩ := exists_rat_btwn (show max a (t - δ / 2) < t by
      exact max_lt ht.1 (by linarith))
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn (show t < min b (t + δ / 2) by
      exact lt_min ht.2 (by linarith))
    have hap' : a < (p : ℝ) := (le_max_left _ _).trans_lt hap
    have hqb' : (q : ℝ) < b := hqb.trans_le (min_le_left _ _)
    have hpq : (p : ℝ) < (q : ℝ) := hpt.trans htq
    have hsub : g '' Icc (p : ℝ) (q : ℝ) ⊆ ball (g t) ε := by
      rintro _ ⟨s, hs, rfl⟩
      apply hcont
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2, le_max_right a (t - δ / 2),
        min_le_right b (t + δ / 2)]
    have hhull := planarFilledHull_subset_convex (convex_ball (g t) ε)
      (nonempty_ball.mpr hε) hsub
    have hmem : f t ∈ planarFilledHull (f '' Icc (p : ℝ) (q : ℝ)) :=
      Or.inl ⟨t, ⟨hpt.le, htq.le⟩, rfl⟩
    rw [h p q hap' hpq hqb'] at hmem
    exact (hhull hmem).le
  have hclosed : IsClosed {t | f t = g t} := isClosed_eq hf hg
  have hsub := closure_minimal hinterior hclosed
  rw [closure_Ioo hab.ne] at hsub
  exact hsub

end LatticeProb
