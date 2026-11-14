import LatticeProb.Topology.AsymmetricKnotComparison

/-!
# Comparison of stopped anchors

A common-prefix estimate and control of the remaining anchors after the first
stop imply the padded-anchor estimate used in finite knot comparisons.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.KnotReparam

/-- Bounds before the earlier stopping index and on the longer remaining
sequence imply a bound on all pairs of stopped anchors. -/
theorem dist_stopped_anchors_le_of_common_prefix
    {E : Type*} [PseudoMetricSpace E] (p q : ℕ → E) (N M : ℕ)
    {δ η : ℝ} (hη : 0 ≤ η)
    (hcommon : ∀ i ≤ min N M, dist (p i) (q i) ≤ δ)
    (hp : ∀ i, M ≤ i → i ≤ N → dist (p i) (p M) ≤ η)
    (hq : ∀ i, N ≤ i → i ≤ M → dist (q N) (q i) ≤ η)
    (i : ℕ) : dist (p (min i N)) (q (min i M)) ≤ δ + η := by
  by_cases hNM : N ≤ M
  · by_cases hi : i ≤ N
    · rw [min_eq_left hi, min_eq_left (hi.trans hNM)]
      exact (hcommon i (le_min hi (hi.trans hNM))).trans (le_add_of_nonneg_right hη)
    · have hNi : N ≤ i := le_of_not_ge hi
      rw [min_eq_right hNi]
      have hq' := hq (min i M) (le_min hNi hNM) (min_le_right _ _)
      have hc := hcommon N (le_min le_rfl hNM)
      exact (dist_triangle _ _ _).trans (add_le_add hc hq')
  · have hMN : M ≤ N := le_of_not_ge hNM
    by_cases hi : i ≤ M
    · rw [min_eq_left (hi.trans hMN), min_eq_left hi]
      exact (hcommon i (le_min (hi.trans hMN) hi)).trans (le_add_of_nonneg_right hη)
    · have hMi : M ≤ i := le_of_not_ge hi
      rw [min_eq_right hMi]
      have hp' := hp (min i N) (le_min hMi hMN) (min_le_right _ _)
      have hc := hcommon M (le_min hMN le_rfl)
      calc
        dist (p (min i N)) (q M) ≤ dist (p (min i N)) (p M) + dist (p M) (q M) :=
          dist_triangle _ _ _
        _ ≤ η + δ := add_le_add hp' hc
        _ = δ + η := add_comm _ _

/-- Compare finite stopped knot paths using common-prefix anchor bounds and
oscillation bounds for whichever anchor sequence stops later. -/
theorem exists_orderIso_dist_le_of_common_prefix
    {E : Type*} [PseudoMetricSpace E] {f g : ℝ≥0 → E}
    {τ σ : ℕ → ℝ≥0} {N M K : ℕ} (hNK : N ≤ K) (hMK : M ≤ K)
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hσ : ∀ n < M, σ n < σ (n + 1))
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) {p q : ℕ → E} {a δ η : ℝ}
    (hη : 0 ≤ η) (hcommon : ∀ i ≤ min N M, dist (p i) (q i) ≤ δ)
    (hp : ∀ i, M ≤ i → i ≤ N → dist (p i) (p M) ≤ η)
    (hq : ∀ i, N ≤ i → i ≤ M → dist (q N) (q i) ≤ η)
    (hf : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n < M, ∀ t ∈ Ico (σ n) (σ (n + 1)), dist (g t) (q n) ≤ a)
    (hfN : ∀ t, τ N ≤ t → dist (f t) (p N) ≤ a)
    (hgM : ∀ t, σ M ≤ t → dist (g t) (q M) ≤ a) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, (∀ n ≤ min N M, φ (τ n) = σ n) ∧
      ∀ t, dist (f t) (g (φ t)) ≤ a + (δ + η) + a := by
  apply exists_orderIso_dist_le_of_asymmetric_finite_knots hNK hMK hτ hσ hτ0 hσ0
    (δ := δ + η) _ hf hg hfN hgM
  intro i _
  exact dist_stopped_anchors_le_of_common_prefix p q N M hη hcommon hp hq i

end LatticeProb.KnotReparam
