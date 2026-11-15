import LatticeProb.Topology.PlanarFilledHull

/-! # Reconstruction from shrinking filled covers -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A closed planar set is recovered from the filled hulls of covers whose pieces
    are arbitrarily small and centered at points of the set. -/
theorem eq_iInter_iUnion_planarFilledHull_of_shrinking_cover
    {K : Set ℂ} {ι : ℕ → Type*} (S : ∀ n, ι n → Set ℂ)
    (hK : IsClosed K) (hcover : ∀ n, K ⊆ ⋃ j, S n j)
    (hsmall : ∀ ε > 0, ∃ n, ∀ j, ∃ x ∈ K, S n j ⊆ Metric.ball x ε) :
    K = ⋂ n, ⋃ j, planarFilledHull (S n j) := by
  apply Subset.antisymm
  · intro z hz
    simp only [mem_iInter, mem_iUnion]
    intro n
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover n hz)
    exact ⟨j, Or.inl hj⟩
  · intro z hz
    apply hK.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := hsmall ε hε
    obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hz n)
    obtain ⟨x, hx, hS⟩ := hn j
    have hball : (Metric.ball x ε).Nonempty := ⟨x, Metric.mem_ball_self hε⟩
    have hzball := planarFilledHull_subset_convex (convex_ball x ε) hball hS hj
    exact ⟨x, hx, by simpa only [Metric.mem_ball, dist_comm] using hzball⟩

end LatticeProb
