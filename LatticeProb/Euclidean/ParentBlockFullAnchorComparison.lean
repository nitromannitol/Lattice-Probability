import LatticeProb.Euclidean.ParentBlockCollarPrefixComparison
import LatticeProb.Topology.StoppedKnotTailTransfer

/-! # Stopped parent-block paths with full-anchor bounds -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- Full-knot common-prefix and remaining-tail bounds control stopped paths
whose segments lie in parent-block collars. -/
theorem exists_orderIso_dist_le_of_parentBlock_collars_full_anchors
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (T S : ℝ≥0) (K L : ℕ)
    (c d : ℕ → ℂ) (s r u v δ η : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v) (hη : 0 ≤ η)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hT : T ≤ τ K) (hS : S ≤ σ L)
    (hτ : ∀ n < K, τ n < T → τ n < τ (n + 1))
    (hσ : ∀ n < L, σ n < S → σ n < σ (n + 1))
    (hfstart : ∀ n < K, f (τ n) ∈ closedSquare (c n) s)
    (hgstart : ∀ n < L, g (σ n) ∈ closedSquare (d n) u)
    (hfcollar : ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      f t ∈ Metric.cthickening r (parentBlock (c n) s))
    (hgcollar : ∀ n < L, ∀ t ∈ Icc (σ n) (σ (n + 1)),
      g t ∈ Metric.cthickening v (parentBlock (d n) u))
    (hanchors : ∀ N ≤ K, ∀ M ≤ L,
      min (τ N) T = T → min (σ M) S = S →
      (∀ n < N, min (τ n) T < min (τ (n + 1)) T) →
      (∀ n < M, min (σ n) S < min (σ (n + 1)) S) →
      (∀ i ≤ min N M, dist (f (τ i)) (g (σ i)) ≤ δ) ∧
      (∀ i, M ≤ i → i ≤ N → dist (f (τ i)) (f (τ M)) ≤ η) ∧
      (∀ i, N ≤ i → i ≤ M → dist (g (σ N)) (g (σ i)) ≤ η)) :
    ∃ N ≤ K, ∃ M ≤ L, ∃ φ : ℝ≥0 ≃o ℝ≥0,
      min (τ N) T = T ∧ min (σ M) S = S ∧
      (∀ n < N, min (τ n) T < min (τ (n + 1)) T) ∧
      (∀ n < M, min (σ n) S < min (σ (n + 1)) S) ∧
      (∀ n ≤ min N M, φ (min (τ n) T) = min (σ n) S) ∧
      ∀ t, dist (f (min t T)) (g (min (φ t) S)) ≤
        max (r + 4 * s) (v + 4 * u) +
          ((2 * (r + 4 * s) + δ + 2 * (v + 4 * u)) +
            max (2 * (r + 4 * s) + η + 2 * (r + 4 * s))
              (2 * (v + 4 * u) + η + 2 * (v + 4 * u))) +
          max (r + 4 * s) (v + 4 * u) := by
  have ha : 0 ≤ r + 4 * s := by positivity
  have hb : 0 ≤ v + 4 * u := by positivity
  have heta : 0 ≤ max (2 * (r + 4 * s) + η + 2 * (r + 4 * s))
      (2 * (v + 4 * u) + η + 2 * (v + 4 * u)) := by positivity
  apply exists_orderIso_dist_le_of_parentBlock_collars_common_prefix f g τ σ T S K L
    c d s r u v _ _ hs hr hu hv heta hτ0 hσ0 hT hS hτ hσ
    hfstart hgstart hfcollar hgcollar
  intro N hNK M hML hN hM hstrict hstrict'
  obtain ⟨hc, hf, hg⟩ := hanchors N hNK M hML hN hM hstrict hstrict'
  apply LatticeProb.KnotReparam.clipped_anchor_bounds_of_full_anchor_bounds
    f g τ σ T S N M (r + 4 * s) (v + 4 * u) δ η
    ha hb hτ0 hσ0 hN hM hstrict hstrict' ?_ ?_ hc hf hg
  · intro n hn t ht
    exact dist_le_of_mem_cthickening_subset_parentBlock hs hr (hfstart n (hn.trans_le hNK))
      Subset.rfl (hfcollar n (hn.trans_le hNK) t ht)
  · intro n hn t ht
    exact dist_le_of_mem_cthickening_subset_parentBlock hu hv (hgstart n (hn.trans_le hML))
      Subset.rfl (hgcollar n (hn.trans_le hML) t ht)

end LatticeProb.ParentBlock
