import LatticeProb.Topology.PlaneTopology

/-!
# Continua avoiding a non-cut point of a Peano continuum

Let `K ⊆ ℂ` be compact and locally connected, and let `x` be a point such that `K \ {x}` is connected (for instance
a point that is not a cut point of the continuum `K`). Then any two points `a, b` of `K \ {x}` lie in a compact
connected subset of `K \ {x}`.

The relation "`y` and `z` lie in a compact connected subset of `K \ {x}`" is symmetric and transitive (take unions),
and it holds near each point `y` of `K \ {x}`: the closure of a small connected neighbourhood of `y` in `K` is compact,
connected and misses `x`. A locally true equivalence relation on a connected set holds everywhere
(`IsPreconnected.induction₂`).

* `exists_isCompact_isPreconnected_subset_diff`: the statement with `K \ {x}` assumed connected.
* `exists_isCompact_isPreconnected_of_not_isCutPoint`: the statement for a non-cut point of a continuum.
-/

open Set Metric

namespace LatticeProb.Topology

/-- In a compact locally connected set `K ⊆ ℂ` with `K \ {x}` connected, any two points of `K \ {x}` lie in a
compact connected subset of `K \ {x}`. -/
theorem exists_isCompact_isPreconnected_subset_diff {K : Set ℂ} (hK : IsCompact K)
    (hKlc : IsLocallyConnectedSet K) {x : ℂ} (hpre : IsPreconnected (K \ {x})) {a b : ℂ}
    (ha : a ∈ K \ {x}) (hb : b ∈ K \ {x}) :
    ∃ H : Set ℂ, IsCompact H ∧ IsPreconnected H ∧ H ⊆ K \ {x} ∧ a ∈ H ∧ b ∈ H := by
  refine hpre.induction₂
    (fun y z => ∃ H : Set ℂ, IsCompact H ∧ IsPreconnected H ∧ H ⊆ K \ {x} ∧ y ∈ H ∧ z ∈ H)
    ?_ ?_ ?_ ha hb
  · intro y hy
    have hyx : 0 < dist y x := dist_pos.2 hy.2
    have hN : K ∩ ball y (dist y x / 2) ∈ nhdsWithin y K :=
      inter_mem_nhdsWithin K (ball_mem_nhds y (half_pos hyx))
    obtain ⟨V, hV, hVsub, hVc⟩ := hKlc y hy.1 _ hN
    have hclK : closure V ⊆ K := closure_minimal (hVsub.trans inter_subset_right) hK.isClosed
    have hclB : closure V ⊆ closedBall y (dist y x / 2) :=
      closure_minimal (fun w hw => ball_subset_closedBall (hVsub hw).1.2) isClosed_closedBall
    have hcl : closure V ⊆ K \ {x} := by
      intro z hz
      refine ⟨hclK hz, fun hzx => ?_⟩
      rw [mem_singleton_iff] at hzx
      have h := hclB hz
      rw [hzx, mem_closedBall, dist_comm] at h
      linarith
    filter_upwards [nhdsWithin_mono y sdiff_subset hV] with z hz
    exact ⟨closure V, hK.of_isClosed_subset isClosed_closure hclK, hVc.isPreconnected.closure, hcl,
      subset_closure (mem_of_mem_nhdsWithin hy.1 hV), subset_closure hz⟩
  · rintro y z w - - - ⟨H₁, hH₁c, hH₁p, hH₁s, hy₁, hz₁⟩ ⟨H₂, hH₂c, hH₂p, hH₂s, hz₂, hw₂⟩
    exact ⟨H₁ ∪ H₂, hH₁c.union hH₂c, IsPreconnected.union z hz₁ hz₂ hH₁p hH₂p, union_subset hH₁s hH₂s,
      Or.inl hy₁, Or.inr hw₂⟩
  · rintro y z - - ⟨H, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨H, h₁, h₂, h₃, h₅, h₄⟩

/-- In a continuum `K ⊆ ℂ` (compact, connected) that is locally connected, any two points other than a non-cut point
`x` lie in a compact connected subset of `K \ {x}`. -/
theorem exists_isCompact_isPreconnected_of_not_isCutPoint {K : Set ℂ} (hK : IsCompact K)
    (hKc : IsConnected K) (hKlc : IsLocallyConnectedSet K) {x : ℂ} (hx : ¬ IsCutPoint K x) {a b : ℂ}
    (ha : a ∈ K \ {x}) (hb : b ∈ K \ {x}) :
    ∃ H : Set ℂ, IsCompact H ∧ IsPreconnected H ∧ H ⊆ K \ {x} ∧ a ∈ H ∧ b ∈ H := by
  have hpre : IsPreconnected (K \ {x}) := by
    by_cases hxK : x ∈ K
    · by_contra h
      exact hx ⟨hxK, h⟩
    · rw [sdiff_singleton_eq_self hxK]
      exact hKc.isPreconnected
  exact exists_isCompact_isPreconnected_subset_diff hK hKlc hpre ha hb

end LatticeProb.Topology
