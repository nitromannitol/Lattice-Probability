import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Compact domains inside an outer region -/

set_option autoImplicit false

open Set Metric Filter

namespace LatticeProb

/-- Uniformly close maps eventually pull a finite family of compact domains
into the same open outer region. -/
theorem eventually_indexedCompact_preimages_subset_outer {E ι J : Type*}
    [MetricSpace E] [Fintype J] (l : Filter ι) (V : ι → Type*)
    (K : J → Set E) (hK : ∀ j, IsCompact (K j))
    {W : Set E} (hW : IsOpen W) (hKW : ∀ j, K j ⊆ W)
    (p q : ∀ i, V i → E)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in l, ∀ v,
      dist (p i v) (q i v) < δ) :
    ∀ᶠ i in l, ∀ j, (p i) ⁻¹' K j ⊆ (p i) ⁻¹' W ∧
      (q i) ⁻¹' K j ⊆ (p i) ⁻¹' W := by
  have hq (j : J) : ∀ᶠ i in l, (q i) ⁻¹' K j ⊆ (p i) ⁻¹' W := by
    obtain ⟨δ, hδ, hδW⟩ := (hK j).exists_thickening_subset_open hW (hKW j)
    filter_upwards [hclose δ hδ] with i hi
    intro v hv
    exact hδW (Metric.mem_thickening_iff.mpr ⟨q i v, hv, hi v⟩)
  filter_upwards [Filter.eventually_all.mpr hq] with i hi
  intro j
  exact ⟨fun _ hv => hKW j hv, hi j⟩

/-- A common shift makes the compact-domain containments hold at every index
and preserves each eventual property of the original sequence. -/
theorem exists_shift_indexedCompact_preimages_subset_outer {E J A : Type*}
    [MetricSpace E] [Fintype J] (V : ℕ → Type*)
    (K : J → Set E) (hK : ∀ j, IsCompact (K j))
    {W : Set E} (hW : IsOpen W) (hKW : ∀ j, K j ⊆ W)
    (p q : ∀ n, V n → E)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v,
      dist (p n v) (q n v) < δ)
    (P : A → ℕ → Prop) (hP : ∀ a, ∀ᶠ n in atTop, P a n) :
    ∃ N : ℕ,
      (∀ n j, (p (n + N)) ⁻¹' K j ⊆ (p (n + N)) ⁻¹' W ∧
        (q (n + N)) ⁻¹' K j ⊆ (p (n + N)) ⁻¹' W) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v,
        dist (p (n + N) v) (q (n + N) v) < δ) ∧
      (∀ a, ∀ᶠ n in atTop, P a (n + N)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_indexedCompact_preimages_subset_outer atTop V K hK hW hKW p q hclose)
  refine ⟨N, ?_, ?_, ?_⟩
  · intro n j
    exact hN (n + N) (Nat.le_add_left N n) j
  · intro δ hδ
    exact (tendsto_add_atTop_nat N).eventually (hclose δ hδ)
  · intro a
    exact (tendsto_add_atTop_nat N).eventually (hP a)

end LatticeProb
