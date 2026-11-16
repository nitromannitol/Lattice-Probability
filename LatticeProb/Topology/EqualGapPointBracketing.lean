import LatticeProb.Topology.ParameterGapBracketing

/-! # Equal-image gap brackets -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Every point between two retained endpoints is bracketed by retained points
with equal images and no retained point strictly between them. -/
theorem exists_equal_gap_bracketing_point {Y : Type*} (f : ℝ → Y)
    {K : Set ℝ} (hK : IsClosed K) {a b x : ℝ} (ha : a ∈ K) (hb : b ∈ K)
    (hx : x ∈ Icc a b)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v) :
    ∃ s ∈ K, ∃ t ∈ K, s ≤ x ∧ x ≤ t ∧ f s = f t ∧
      ∀ w ∈ K, ¬ (s < w ∧ w < t) := by
  by_cases hxK : x ∈ K
  · exact ⟨x, hxK, x, hxK, le_rfl, le_rfl, rfl, fun _ _ h => (lt_irrefl x) (lt_trans h.1 h.2)⟩
  · have hax : a < x := lt_of_le_of_ne hx.1 (fun h => hxK (h ▸ ha))
    have hxb : x < b := lt_of_le_of_ne hx.2 (fun h => hxK (h ▸ hb))
    have hdis : Disjoint K (Icc x x) := by
      apply disjoint_left.mpr
      intro y hy hyx
      have : y = x := le_antisymm hyx.2 hyx.1
      exact hxK (this ▸ hy)
    obtain ⟨s, hs, t, ht, _, hsx, hxt, _, hbetween⟩ :=
      exists_gap_bracketing_interval K hK ha hb hax le_rfl hxb hdis
    exact ⟨s, hs, t, ht, hsx.le, hxt.le, hgap s hs t ht (lt_trans hsx hxt) hbetween,
      hbetween⟩

end LatticeProb
