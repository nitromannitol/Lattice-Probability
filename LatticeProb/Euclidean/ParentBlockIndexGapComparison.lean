import LatticeProb.Euclidean.ParentBlockAnchorTail
import LatticeProb.Euclidean.ParentBlockFullAnchorComparison

/-! # Stopped parent-block paths with bounded index gaps -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- A uniform bound on the terminal index gap and matching full anchors
controls stopped paths whose segments stay in parent-block collars. -/
theorem exists_orderIso_dist_le_of_parentBlock_collars_index_gap
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (T S : ℝ≥0) (K L J : ℕ)
    (c d : ℕ → ℂ) (s r u v δ : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hT : T ≤ τ K) (hS : S ≤ σ L)
    (hτ : ∀ n < K, τ n < T → τ n < τ (n + 1))
    (hσ : ∀ n < L, σ n < S → σ n < σ (n + 1))
    (hτmono : ∀ n < K, τ n ≤ τ (n + 1))
    (hσmono : ∀ n < L, σ n ≤ σ (n + 1))
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
      N ≤ M + J ∧ M ≤ N + J) :
    ∃ N ≤ K, ∃ M ≤ L, ∃ φ : ℝ≥0 ≃o ℝ≥0,
      min (τ N) T = T ∧ min (σ M) S = S ∧
      (∀ n < N, min (τ n) T < min (τ (n + 1)) T) ∧
      (∀ n < M, min (σ n) S < min (σ (n + 1)) S) ∧
      (∀ n ≤ min N M, φ (min (τ n) T) = min (σ n) S) ∧
      ∀ t, dist (f (min t T)) (g (min (φ t) S)) ≤
        max (r + 4 * s) (v + 4 * u) +
          ((2 * (r + 4 * s) + δ + 2 * (v + 4 * u)) +
            max (2 * (r + 4 * s) + ((J : ℝ) * max (r + 4 * s) (v + 4 * u)) +
                2 * (r + 4 * s))
              (2 * (v + 4 * u) + ((J : ℝ) * max (r + 4 * s) (v + 4 * u)) +
                2 * (v + 4 * u))) +
          max (r + 4 * s) (v + 4 * u) := by
  have hη : 0 ≤ (J : ℝ) * max (r + 4 * s) (v + 4 * u) := by positivity
  apply exists_orderIso_dist_le_of_parentBlock_collars_full_anchors f g τ σ T S K L
    c d s r u v δ _ hs hr hu hv hη hτ0 hσ0 hT hS hτ hσ
    hfstart hgstart hfcollar hgcollar
  intro N hNK M hML hN hM hstrict hstrict'
  obtain ⟨hc, hNM, hMN⟩ := hanchors N hNK M hML hN hM hstrict hstrict'
  have htails := anchor_tails_le_of_parentBlock_collars f g τ σ c d N M J s r u v
    hs hr hu hv
    (fun n hn => hτmono n (hn.trans_le hNK))
    (fun n hn => hσmono n (hn.trans_le hML))
    (fun n hn => hfstart n (hn.trans_le hNK))
    (fun n hn => hgstart n (hn.trans_le hML))
    (fun n hn => hfcollar n (hn.trans_le hNK))
    (fun n hn => hgcollar n (hn.trans_le hML)) hNM hMN
  exact ⟨hc, htails.1, htails.2⟩

end LatticeProb.ParentBlock
