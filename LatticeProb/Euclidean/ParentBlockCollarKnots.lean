import LatticeProb.Euclidean.ParentBlockCollar
import LatticeProb.Topology.StoppedKnotPackage

/-! # Stopped knots for paths in parent-block collars -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- Collar containment on each segment gives a stopped knot package, with a
uniform oscillation bound from the corresponding child-square starting point. -/
theorem exists_stopped_knots_of_parentBlock_collars
    (f : ℝ≥0 → ℂ) (τ : ℕ → ℝ≥0) (T : ℝ≥0) (K : ℕ)
    (centres : ℕ → ℂ) (s r : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hzero : τ 0 = 0) (hreach : T ≤ τ K)
    (hstrict : ∀ n < K, τ n < T → τ n < τ (n + 1))
    (hstart : ∀ n < K, f (τ n) ∈ closedSquare (centres n) s)
    (hcollar : ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      f t ∈ Metric.cthickening r (parentBlock (centres n) s)) :
    ∃ N ≤ K, (min (τ 0) T = 0) ∧ (min (τ N) T = T) ∧
      (∀ n < N, min (τ n) T < min (τ (n + 1)) T) ∧
      (∀ n < N, ∀ t ∈ Ico (min (τ n) T) (min (τ (n + 1)) T),
        dist (f (min t T)) (f (min (τ n) T)) ≤ r + 4 * s) ∧
      (∀ t, min (τ N) T ≤ t → f (min t T) = f T) := by
  apply LatticeProb.KnotReparam.exists_stopped_knot_package f τ T K (r + 4 * s)
    hzero hreach hstrict
  intro n hn t ht
  exact dist_le_of_mem_cthickening_subset_parentBlock hs hr (hstart n hn)
    (Subset.rfl) (hcollar n hn t ht)

end LatticeProb.ParentBlock
