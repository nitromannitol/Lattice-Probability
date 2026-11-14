import LatticeProb.Euclidean.ParentBlockCollarKnots
import LatticeProb.Topology.AsymmetricKnotComparison

/-! # Comparison of stopped paths in parent-block collars -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- Compare two stopped paths using collar bounds and padded stopped anchors.
The anchor hypothesis covers either possible order of the stopping indices. -/
theorem exists_orderIso_dist_le_of_parentBlock_collars
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (T S : ℝ≥0) (K L : ℕ)
    (c d : ℕ → ℂ) (s r u v δ : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v)
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
      ∀ n ≤ max K L,
        dist (f (min (τ (min n N)) T)) (g (min (σ (min n M)) S)) ≤ δ) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (f (min t T)) (g (min (φ t) S)) ≤
        max (r + 4 * s) (v + 4 * u) + δ + max (r + 4 * s) (v + 4 * u) := by
  obtain ⟨N, hNK, hzero, hN, hstrict, hosc, htail⟩ :=
    exists_stopped_knots_of_parentBlock_collars f τ T K c s r hs hr hτ0 hT hτ hfstart hfcollar
  obtain ⟨M, hML, hzero', hM, hstrict', hosc', htail'⟩ :=
    exists_stopped_knots_of_parentBlock_collars g σ S L d u v hu hv hσ0 hS hσ hgstart hgcollar
  let a := max (r + 4 * s) (v + 4 * u)
  have ha : 0 ≤ a := le_trans (by positivity : 0 ≤ r + 4 * s) (le_max_left _ _)
  obtain ⟨φ, _, hφ⟩ :=
    LatticeProb.KnotReparam.exists_orderIso_dist_le_of_asymmetric_finite_knots
      (N := N) (M := M) (K := max K L)
      (hNK.trans (le_max_left _ _)) (hML.trans (le_max_right _ _))
      hstrict hstrict' hzero hzero'
      (p := fun n => f (min (τ n) T)) (q := fun n => g (min (σ n) S))
      (hanchors N hNK M hML hN hM hstrict hstrict')
      (fun n hn t ht => (hosc n hn t ht).trans (le_max_left _ _))
      (fun n hn t ht => (hosc' n hn t ht).trans (le_max_right _ _))
      (fun t ht => by rw [htail t ht, hN, dist_self]; exact ha)
      (fun t ht => by rw [htail' t ht, hM, dist_self]; exact ha)
  exact ⟨φ, hφ⟩

end LatticeProb.ParentBlock
