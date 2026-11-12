import LatticeProb.Topology.BiinfiniteChain
import LatticeProb.Topology.BiinfiniteChainLocal
import LatticeProb.Topology.PolygonalLocalSides
import LatticeProb.Topology.CrosscutAssembly

/-!
# Simple bi-infinite polygonal chains as two-sided crosscuts

Let `u : ℤ → ℂ` with `u n → a` as `n → -∞` and `u n → b` as `n → +∞`, such that the bi-infinite polygonal chain
`⋃ n, [u n, u (n + 1)]` is simple and avoids `a ≠ b`. If all its segments lie in an open set `C`, the chain is a
crosscut of `C` from `a` to `b` in the following strong form: it has a parametrisation `f` that is continuous and
injective on `[0, 1]` with `f 0 = a`, `f 1 = b` and `f '' (0, 1) ⊆ C`; every interior point of the arc has a disk
in `C` that the arc splits into two preconnected sides, each having the arc in that disk in its closure; and the arc
is straight near some interior point.

## Main statements

* `exists_crosscut_of_simple_biinfinite`.
* `torhorstSimpleLoop_of_simple_biinfinite_chains`: Torhorst's theorem follows once any two distinct frontier
  points of a complementary component of a Peano continuum without cut points are joined through the component
  by a simple bi-infinite polygonal chain.
-/

open Set Filter Metric
open scoped Topology

namespace LatticeProb.Topology

/-- Agreement of two sets on a ball passes to smaller concentric balls. -/
theorem inter_ball_eq_of_inter_ball_eq_of_le {α : Type*} [PseudoMetricSpace α] {A B : Set α} {y : α}
    {r r' : ℝ} (h : A ∩ ball y r = B ∩ ball y r) (hr : r' ≤ r) : A ∩ ball y r' = B ∩ ball y r' := by
  have hsub : ball y r' ⊆ ball y r := ball_subset_ball hr
  rw [← inter_eq_right.2 hsub, ← inter_assoc, h, inter_assoc]

/-- **A simple bi-infinite polygonal chain in an open set is a two-sided crosscut.** If consecutive vertices are
distinct, consecutive segments meet only in their common vertex, segments two or more apart are disjoint, the chain
avoids its limits `a ≠ b` and all its segments lie in the open set `C`, then its parametrisation is an arc from `a`
to `b` through `C`, locally two-sided at each interior point, and straight near some interior point. -/
theorem exists_crosscut_of_simple_biinfinite {C : Set ℂ} (hC : IsOpen C) {u : ℤ → ℂ} {a b : ℂ}
    (hne : ∀ n, u n ≠ u (n + 1))
    (hadj : ∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)})
    (hfar : ∀ n m : ℤ, n + 2 ≤ m →
      Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1))))
    (ha : Tendsto u atBot (𝓝 a)) (hb : Tendsto u atTop (𝓝 b))
    (haγ : ∀ n, a ∉ segment ℝ (u n) (u (n + 1))) (hbγ : ∀ n, b ∉ segment ℝ (u n) (u (n + 1)))
    (hab : a ≠ b) (huC : ∀ n, segment ℝ (u n) (u (n + 1)) ⊆ C) :
    ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f 0 = a ∧ f 1 = b ∧
      f '' Ioo 0 1 ⊆ C ∧
      (∀ y ∈ f '' Ioo 0 1, ∃ r > 0, ball y r ⊆ C ∧ ∃ P₁ P₂ : Set ℂ, IsPreconnected P₁ ∧
        IsPreconnected P₂ ∧ ball y r \ f '' Icc 0 1 = P₁ ∪ P₂ ∧
        f '' Icc 0 1 ∩ ball y r ⊆ closure P₁ ∩ closure P₂) ∧
      ∃ t₀ ∈ Ioo (0 : ℝ) 1, ∃ r > 0, ∃ c d : ℂ, f t₀ ∈ openSegment ℝ c d ∧ r ≤ ‖c - f t₀‖ ∧
        r ≤ ‖d - f t₀‖ ∧ ball (f t₀) r ⊆ C ∧
        f '' Icc 0 1 ∩ ball (f t₀) r = segment ℝ c d ∩ ball (f t₀) r := by
  obtain ⟨f, hfc, hf⟩ := exists_biinfiniteChain_param ha hb
  have hIoo := hf.image_Ioo
  have hIcc := hf.image_Icc
  have hγC : f '' Ioo 0 1 ⊆ C := by
    rw [hIoo]
    exact iUnion_subset huC
  have hball : ∀ y ∈ f '' Ioo 0 1, ∃ ε > 0, ball y ε ⊆ C := fun y hy =>
    Metric.isOpen_iff.1 hC y (hγC hy)
  refine ⟨f, hfc, hf.injOn hne hadj hfar haγ hbγ hab, hf.apply_zero, hf.apply_one, hγC, ?_, ?_⟩
  · intro y hy
    obtain ⟨ε, hε, hεC⟩ := hball y hy
    rw [hIoo, mem_iUnion] at hy
    obtain ⟨k, hk⟩ := hy
    obtain ⟨r, hr, c, d, hc, hd, hcd, hrc, hrd, hγ⟩ :=
      exists_two_segments_inter_ball_of_simple_biinfinite hne hadj hfar ha hb haγ hbγ hk
    refine ⟨min r ε, lt_min hr hε, (ball_subset_ball (min_le_right _ _)).trans hεC, ?_⟩
    rw [hIcc]
    exact exists_sides_of_inter_ball_eq_two_segments hc hd hcd (lt_min hr hε)
      ((min_le_left _ _).trans hrc) ((min_le_left _ _).trans hrd)
      (inter_ball_eq_of_inter_ball_eq_of_le hγ (min_le_left _ _))
  · obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℂ, y₀ ∈ openSegment ℝ (u 0) (u (0 + 1)) :=
      ⟨_, 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have hy₀γ : y₀ ∈ f '' Ioo 0 1 := by
      rw [hIoo]
      exact mem_iUnion.2 ⟨0, openSegment_subset_segment ℝ _ _ hy₀⟩
    obtain ⟨ε, hε, hεC⟩ := hball y₀ hy₀γ
    obtain ⟨t₀, ht₀, hft₀⟩ := hy₀γ
    obtain ⟨r, hr, hrc, hrd, hγ⟩ :=
      exists_inter_ball_eq_segment_of_simple_biinfinite hne hadj hfar ha hb haγ hbγ hy₀
    refine ⟨t₀, ht₀, min r ε, lt_min hr hε, u 0, u (0 + 1), ?_⟩
    rw [hft₀, hIcc]
    exact ⟨hy₀, (min_le_left _ _).trans hrc, (min_le_left _ _).trans hrd,
      (ball_subset_ball (min_le_right _ _)).trans hεC,
      inter_ball_eq_of_inter_ball_eq_of_le hγ (min_le_left _ _)⟩

/-- **Torhorst's theorem from simple bi-infinite chains.** If, for every nondegenerate Peano continuum `K ⊆ ℂ`
without cut points, any two distinct frontier points `a`, `b` of a component `C` of `ℂ \ K` are the limits at
`-∞` and `+∞` of a simple bi-infinite polygonal chain whose segments lie in `C` and avoid `a` and `b`, then the
frontier of every complementary component of such a continuum is a simple closed curve. -/
theorem torhorstSimpleLoop_of_simple_biinfinite_chains
    (hChain : ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
      (∀ x : ℂ, ¬ IsCutPoint K x) → ∀ C ∈ connectedComponentsIn Kᶜ, ∀ a ∈ frontier C, ∀ b ∈ frontier C,
      a ≠ b → ∃ u : ℤ → ℂ, (∀ n, u n ≠ u (n + 1)) ∧
        (∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)}) ∧
        (∀ n m : ℤ, n + 2 ≤ m → Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1)))) ∧
        Tendsto u atBot (𝓝 a) ∧ Tendsto u atTop (𝓝 b) ∧
        (∀ n, a ∉ segment ℝ (u n) (u (n + 1))) ∧ (∀ n, b ∉ segment ℝ (u n) (u (n + 1))) ∧
        ∀ n, segment ℝ (u n) (u (n + 1)) ⊆ C) :
    TorhorstSimpleLoop :=
  torhorstSimpleLoop_of_locallyPolygonal_crosscuts fun K hK hKc hKn hKlc hcut C hC a ha b hb hab => by
    obtain ⟨u, hne, hadj, hfar, hua, hub, haγ, hbγ, huC⟩ := hChain K hK hKc hKn hKlc hcut C hC a ha b hb hab
    exact exists_crosscut_of_simple_biinfinite (isOpen_of_mem_connectedComponentsIn_compl hK.isClosed hC)
      hne hadj hfar hua hub haγ hbγ hab huC

end LatticeProb.Topology
