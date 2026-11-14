import LatticeProb.Topology.ClippedAnchorComparison
import LatticeProb.Topology.StoppedKnotPackage

/-! # Displacement of clipped knot anchors -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.KnotReparam

/-- Segment oscillation controls the displacement caused by clipping any
anchor at the first stopping knot. -/
theorem dist_clipped_knot_le_of_oscillation
    {E : Type*} [PseudoMetricSpace E] (f : ℝ≥0 → E) (τ : ℕ → ℝ≥0)
    (T : ℝ≥0) (N : ℕ) (a : ℝ) (ha : 0 ≤ a) (hzero : τ 0 = 0)
    (hN : min (τ N) T = T)
    (hstrict : ∀ n < N, min (τ n) T < min (τ (n + 1)) T)
    (hosc : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      dist (f t) (f (τ n)) ≤ a)
    (i : ℕ) (hi : i ≤ N) : dist (f (min (τ i) T)) (f (τ i)) ≤ 2 * a := by
  by_cases hiN : i < N
  · have hlt : min (τ i) T < T := lt_of_lt_of_le (hstrict i hiN) (min_le_right _ _)
    have hτ : τ i < T := by
      by_contra h
      have : min (τ i) T = T := min_eq_right (le_of_not_gt h)
      rw [this] at hlt
      exact lt_irrefl _ hlt
    rw [min_eq_left (le_of_lt hτ), dist_self]
    linarith
  · have hiEq : i = N := le_antisymm hi (le_of_not_gt hiN)
    subst i
    cases N with
    | zero =>
      rw [hzero, zero_min, dist_self]
      linarith
    | succ n =>
      have hn : n < n + 1 := Nat.lt_succ_self n
      have hlt : min (τ n) T < T := by simpa [hN] using hstrict n hn
      have hτn : τ n < T := by
        by_contra h
        have : min (τ n) T = T := min_eq_right (le_of_not_gt h)
        rw [this] at hlt
        exact lt_irrefl _ hlt
      have hT : T ≤ τ (n + 1) := min_eq_right_iff.mp hN
      have hfirst := hosc n hn T ⟨le_of_lt hτn, hT⟩
      have hlast := hosc n hn (τ (n + 1)) ⟨(le_of_lt hτn).trans hT, le_rfl⟩
      rw [hN]
      calc
        dist (f T) (f (τ (n + 1))) ≤
            dist (f T) (f (τ n)) + dist (f (τ n)) (f (τ (n + 1))) := dist_triangle _ _ _
        _ ≤ a + a := add_le_add hfirst (by simpa [dist_comm] using hlast)
        _ = 2 * a := by ring

/-- Matching full anchors implies matching clipped anchors, with an explicit
error for each path's terminal clipping displacement. -/
theorem dist_clipped_knots_le_of_oscillation
    {E : Type*} [PseudoMetricSpace E] (f g : ℝ≥0 → E)
    (τ σ : ℕ → ℝ≥0) (T S : ℝ≥0) (N M : ℕ) (a b δ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hN : min (τ N) T = T) (hM : min (σ M) S = S)
    (hτ : ∀ n < N, min (τ n) T < min (τ (n + 1)) T)
    (hσ : ∀ n < M, min (σ n) S < min (σ (n + 1)) S)
    (hf : ∀ n < N, ∀ t ∈ Icc (τ n) (τ (n + 1)), dist (f t) (f (τ n)) ≤ a)
    (hg : ∀ n < M, ∀ t ∈ Icc (σ n) (σ (n + 1)), dist (g t) (g (σ n)) ≤ b)
    (hmatch : ∀ i ≤ min N M, dist (f (τ i)) (g (σ i)) ≤ δ)
    (i : ℕ) (hi : i ≤ min N M) :
    dist (f (min (τ i) T)) (g (min (σ i) S)) ≤ 2 * a + δ + 2 * b := by
  apply dist_clipped_anchors_le_of_unclipped _ _ _ _ (min N M) _ _ hmatch i hi
  · intro j hj
    exact dist_clipped_knot_le_of_oscillation f τ T N a ha hτ0 hN hτ hf j
      (hj.trans (min_le_left _ _))
  · intro j hj
    simpa [dist_comm] using dist_clipped_knot_le_of_oscillation g σ S M b hb hσ0 hM hσ hg j
      (hj.trans (min_le_right _ _))

end LatticeProb.KnotReparam
