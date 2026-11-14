import Mathlib

/-!
# Countability of local minima

A real function whose distinct local minima have distinct values has at most
countably many local-minimum times. Continuity is not required.
-/

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Distinct values at distinct local minima imply that the set of local-minimum
points is countable. -/
theorem countable_localMin_of_distinct_values (f : ℝ → ℝ)
    (hdist : ∀ a b, a ≠ b → IsLocalMin f a → IsLocalMin f b → f a ≠ f b) :
    {t | IsLocalMin f t}.Countable := by
  let A : ℚ × ℚ → Set ℝ := fun pq =>
    {t | IsLocalMin f t ∧ t ∈ Ioo (pq.1 : ℝ) (pq.2 : ℝ) ∧
      ∀ u ∈ Ioo (pq.1 : ℝ) (pq.2 : ℝ), f t ≤ f u}
  have hcover : {t | IsLocalMin f t} ⊆ ⋃ pq, A pq := by
    intro t ht
    obtain ⟨a, b, ⟨hat, htb⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ht
    obtain ⟨p, hap, hpt⟩ := exists_rat_btwn hat
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
    refine mem_iUnion.mpr ⟨(p, q), ht, ⟨hpt, htq⟩, ?_⟩
    intro u hu
    exact hsub ⟨hap.trans hu.1, hu.2.trans hqb⟩
  refine Set.Countable.mono hcover ?_
  apply countable_iUnion
  intro pq
  apply Subsingleton.countable
  intro a ha b hb
  by_contra hne
  exact hdist a b hne ha.1 hb.1 (le_antisymm (ha.2.2 b hb.2.1) (hb.2.2 a ha.2.1))

end LatticeProb
