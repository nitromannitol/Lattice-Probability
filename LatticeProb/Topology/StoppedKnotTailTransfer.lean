import LatticeProb.Topology.StoppedKnotClipping

/-! # Tail bounds for clipped knot anchors -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.KnotReparam

/-- An oscillation bound transfers an estimate between full knot anchors to
an estimate between the corresponding stopped anchors. -/
theorem dist_clipped_knots_le_of_full_anchor_bound
    {E : Type*} [PseudoMetricSpace E] (f : ℝ≥0 → E) (τ : ℕ → ℝ≥0)
    (T : ℝ≥0) (N : ℕ) (a η : ℝ) (ha : 0 ≤ a) (hzero : τ 0 = 0)
    (hN : min (τ N) T = T)
    (hstrict : ∀ n < N, min (τ n) T < min (τ (n + 1)) T)
    (hosc : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      dist (f t) (f (τ n)) ≤ a)
    (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N)
    (hbound : dist (f (τ i)) (f (τ j)) ≤ η) :
    dist (f (min (τ i) T)) (f (min (τ j) T)) ≤ 2 * a + η + 2 * a := by
  have hi' := dist_clipped_knot_le_of_oscillation f τ T N a ha hzero hN hstrict hosc i hi
  have hj' := dist_clipped_knot_le_of_oscillation f τ T N a ha hzero hN hstrict hosc j hj
  calc
    dist (f (min (τ i) T)) (f (min (τ j) T)) ≤
        dist (f (min (τ i) T)) (f (τ i)) + dist (f (τ i)) (f (τ j)) +
          dist (f (τ j)) (f (min (τ j) T)) := by
      exact (dist_triangle (f (min (τ i) T)) (f (τ j)) (f (min (τ j) T))).trans
        (add_le_add (dist_triangle (f (min (τ i) T)) (f (τ i)) (f (τ j))) le_rfl)
    _ ≤ 2 * a + η + 2 * a := by
      exact add_le_add (add_le_add hi' hbound) (by simpa only [dist_comm] using hj')

/-- Full-anchor common-prefix and remaining-tail bounds imply the corresponding
bounds for two separately stopped knot sequences. -/
theorem clipped_anchor_bounds_of_full_anchor_bounds
    {E : Type*} [PseudoMetricSpace E] (f g : ℝ≥0 → E)
    (τ σ : ℕ → ℝ≥0) (T S : ℝ≥0) (N M : ℕ) (a b δ η : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hN : min (τ N) T = T) (hM : min (σ M) S = S)
    (hτ : ∀ n < N, min (τ n) T < min (τ (n + 1)) T)
    (hσ : ∀ n < M, min (σ n) S < min (σ (n + 1)) S)
    (hf : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)), dist (f t) (f (τ n)) ≤ a)
    (hg : ∀ n < M, ∀ t ∈ Icc (σ n) (σ (n + 1)), dist (g t) (g (σ n)) ≤ b)
    (hcommon : ∀ i ≤ min N M, dist (f (τ i)) (g (σ i)) ≤ δ)
    (hftail : ∀ i, M ≤ i → i ≤ N → dist (f (τ i)) (f (τ M)) ≤ η)
    (hgtail : ∀ i, N ≤ i → i ≤ M → dist (g (σ N)) (g (σ i)) ≤ η) :
    (∀ i ≤ min N M, dist (f (min (τ i) T)) (g (min (σ i) S)) ≤
      2 * a + δ + 2 * b) ∧
    (∀ i, M ≤ i → i ≤ N → dist (f (min (τ i) T)) (f (min (τ M) T)) ≤
      max (2 * a + η + 2 * a) (2 * b + η + 2 * b)) ∧
    (∀ i, N ≤ i → i ≤ M → dist (g (min (σ N) S)) (g (min (σ i) S)) ≤
      max (2 * a + η + 2 * a) (2 * b + η + 2 * b)) := by
  refine ⟨dist_clipped_knots_le_of_oscillation f g τ σ T S N M a b δ
    ha hb hτ0 hσ0 hN hM hτ hσ hf hg hcommon, ?_, ?_⟩
  · intro i hMi hiN
    exact (dist_clipped_knots_le_of_full_anchor_bound f τ T N a η ha hτ0 hN hτ hf
      i M hiN (hMi.trans hiN) (hftail i hMi hiN)).trans (le_max_left _ _)
  · intro i hNi hiM
    exact (dist_clipped_knots_le_of_full_anchor_bound g σ S M b η hb hσ0 hM hσ hg
      N i (hNi.trans hiM) hiM (hgtail i hNi hiM)).trans (le_max_right _ _)

end LatticeProb.KnotReparam
