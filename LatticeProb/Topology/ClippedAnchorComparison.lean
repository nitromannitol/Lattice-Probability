import LatticeProb.Topology.StoppedAnchorComparison

/-!
# Comparison of clipped anchors

Whole-excursion endpoint bounds transfer to clipped endpoints when their
respective displacements are controlled.
-/

set_option autoImplicit false

namespace LatticeProb.KnotReparam

/-- Bounds for corresponding whole-excursion anchors and for the two
clipping displacements imply bounds for corresponding clipped anchors. -/
theorem dist_clipped_anchors_le_of_unclipped
    {E : Type*} [PseudoMetricSpace E] (p q P Q : ℕ → E) (K : ℕ)
    {a b δ : ℝ}
    (hp : ∀ i ≤ K, dist (p i) (P i) ≤ a)
    (hq : ∀ i ≤ K, dist (Q i) (q i) ≤ b)
    (hmatch : ∀ i ≤ K, dist (P i) (Q i) ≤ δ)
    (i : ℕ) (hi : i ≤ K) : dist (p i) (q i) ≤ a + δ + b :=
  (dist_triangle4 (p i) (P i) (Q i) (q i)).trans
    (add_le_add (add_le_add (hp i hi) (hmatch i hi)) (hq i hi))

/-- Clipped common-prefix anchors and an explicit bound on the longer
remaining sequence give a bound on every pair of padded stopped anchors. -/
theorem dist_stopped_clipped_anchors_le
    {E : Type*} [PseudoMetricSpace E] (p q P Q : ℕ → E) (N M : ℕ)
    {a b δ η : ℝ} (hη : 0 ≤ η)
    (hpclip : ∀ i ≤ min N M, dist (p i) (P i) ≤ a)
    (hqclip : ∀ i ≤ min N M, dist (Q i) (q i) ≤ b)
    (hmatch : ∀ i ≤ min N M, dist (P i) (Q i) ≤ δ)
    (hp : ∀ i, M ≤ i → i ≤ N → dist (p i) (p M) ≤ η)
    (hq : ∀ i, N ≤ i → i ≤ M → dist (q N) (q i) ≤ η)
    (i : ℕ) : dist (p (min i N)) (q (min i M)) ≤ (a + δ + b) + η := by
  apply dist_stopped_anchors_le_of_common_prefix p q N M hη _ hp hq i
  exact dist_clipped_anchors_le_of_unclipped p q P Q (min N M) hpclip hqclip hmatch

end LatticeProb.KnotReparam
