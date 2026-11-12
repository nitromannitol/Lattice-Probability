import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cells of a curve parametrized by area

Let `η : ℝ → X` be a continuous curve and `μ` a measure on `X` with `μ (η '' [a, b]) = b - a` for
all `a < b` (the curve is parametrized by `μ`-area). The images of two intervals with disjoint
interiors meet in a `μ`-null set. If moreover `η` is onto, every nonempty open set has positive
`μ`-measure, so such images share no nonempty open set. For the cells `η([ε (k - 1), ε k])`,
`k ∈ ℤ`, of a space-filling curve this means that open sets contained in distinct cells (for
instance their inballs) are pairwise disjoint, whether or not `μ` is absolutely continuous with
respect to a reference measure.

## Main results

* `LatticeProb.measure_image_Icc_inter_image_Icc_eq_zero`
* `LatticeProb.measure_pos_of_isOpen_of_surjective`
* `LatticeProb.eq_empty_of_isOpen_subset_image_Icc_inter`
* `LatticeProb.pairwiseDisjoint_of_isOpen_subset_cell`
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X} {η : ℝ → X}

/-- The images of two intervals with disjoint interiors under a continuous curve parametrized by
`μ`-area meet in a `μ`-null set. -/
theorem measure_image_Icc_inter_image_Icc_eq_zero [T2Space X] [OpensMeasurableSpace X]
    (hc : Continuous η) (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    μ (η '' Icc a b ∩ η '' Icc c d) = 0 := by
  have hfin : μ (η '' Icc a d) ≠ ⊤ := by
    rw [hμ a d (by linarith)]; exact ENNReal.ofReal_ne_top
  have hkey : μ (η '' Icc a b ∩ η '' Icc c d) + μ (η '' Icc a d) ≤ 0 + μ (η '' Icc a d) := by
    rw [zero_add]
    have hmC : MeasurableSet (η '' Icc c d) :=
      (isCompact_Icc.image hc).isClosed.measurableSet
    rcases hbc.lt_or_eq with hbc | hbc
    · have hcover : η '' Icc a d ⊆ (η '' Icc a b ∪ η '' Icc c d) ∪ η '' Icc b c := by
        rintro _ ⟨t, ht, rfl⟩
        rcases le_total t b with htb | htb
        · exact Or.inl (Or.inl ⟨t, ⟨ht.1, htb⟩, rfl⟩)
        rcases le_total t c with htc | htc
        · exact Or.inr ⟨t, ⟨htb, htc⟩, rfl⟩
        · exact Or.inl (Or.inr ⟨t, ⟨htc, ht.2⟩, rfl⟩)
      calc μ (η '' Icc a b ∩ η '' Icc c d) + μ (η '' Icc a d)
          ≤ μ (η '' Icc a b ∩ η '' Icc c d) +
              (μ (η '' Icc a b ∪ η '' Icc c d) + μ (η '' Icc b c)) := by
            gcongr
            exact (measure_mono hcover).trans (measure_union_le _ _)
        _ = μ (η '' Icc a b) + μ (η '' Icc c d) + μ (η '' Icc b c) := by
            rw [← add_assoc, add_comm (μ (η '' Icc a b ∩ η '' Icc c d))
              (μ (η '' Icc a b ∪ η '' Icc c d)), measure_union_add_inter _ hmC]
        _ = μ (η '' Icc a d) := by
            rw [hμ a b hab, hμ c d hcd, hμ b c hbc, hμ a d (by linarith),
              ← ENNReal.ofReal_add (by linarith) (by linarith),
              ← ENNReal.ofReal_add (by linarith) (by linarith)]
            congr 1
            ring
    · rw [hbc] at hab ⊢
      have hcover : η '' Icc a d ⊆ η '' Icc a c ∪ η '' Icc c d := by
        rintro _ ⟨t, ht, rfl⟩
        rcases le_total t c with htc | htc
        · exact Or.inl ⟨t, ⟨ht.1, htc⟩, rfl⟩
        · exact Or.inr ⟨t, ⟨htc, ht.2⟩, rfl⟩
      calc μ (η '' Icc a c ∩ η '' Icc c d) + μ (η '' Icc a d)
          ≤ μ (η '' Icc a c ∩ η '' Icc c d) + μ (η '' Icc a c ∪ η '' Icc c d) := by
            gcongr
        _ = μ (η '' Icc a c) + μ (η '' Icc c d) := by
            rw [add_comm, measure_union_add_inter _ hmC]
        _ = μ (η '' Icc a d) := by
            rw [hμ a c hab, hμ c d hcd, hμ a d (by linarith),
              ← ENNReal.ofReal_add (by linarith) (by linarith)]
            congr 1
            ring
  exact le_antisymm (ENNReal.le_of_add_le_add_right hfin hkey) (zero_le)

/-- For a continuous onto curve parametrized by `μ`-area, every nonempty open set has positive
`μ`-measure. -/
theorem measure_pos_of_isOpen_of_surjective (hc : Continuous η) (hs : Surjective η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {O : Set X} (hO : IsOpen O) (hne : O.Nonempty) : 0 < μ O := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, rfl⟩ := hs x
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hO.preimage hc) t hx
  have hsub : η '' Icc t (t + δ / 2) ⊆ O := by
    rintro _ ⟨s, hs', rfl⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs'.1, hs'.2]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (t + δ / 2 - t) := ENNReal.ofReal_pos.2 (by linarith)
    _ = μ (η '' Icc t (t + δ / 2)) := (hμ _ _ (by linarith)).symm
    _ ≤ μ O := measure_mono hsub

/-- For a continuous onto curve parametrized by `μ`-area, an open set contained in the images of
two intervals with disjoint interiors is empty. -/
theorem eq_empty_of_isOpen_subset_image_Icc_inter [T2Space X] [OpensMeasurableSpace X]
    (hc : Continuous η) (hs : Surjective η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b c d : ℝ} (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {O : Set X} (hO : IsOpen O)
    (hsub : O ⊆ η '' Icc a b ∩ η '' Icc c d) : O = ∅ := by
  by_contra hne
  have h0 := measure_pos_of_isOpen_of_surjective hc hs hμ hO (nonempty_iff_ne_empty.2 hne)
  have hle := measure_mono (μ := μ) hsub
  rw [measure_image_Icc_inter_image_Icc_eq_zero hc hμ hab hbc hcd] at hle
  exact absurd (h0.trans_le hle) (lt_irrefl 0)

/-- **Open sets in distinct cells are disjoint.** For a continuous onto curve `η` parametrized by
`μ`-area and `ε > 0`, open sets `O k` contained in the cells `η([ε (k - 1), ε k])` (`k ∈ s`) are
pairwise disjoint. -/
theorem pairwiseDisjoint_of_isOpen_subset_cell [T2Space X] [OpensMeasurableSpace X]
    (hc : Continuous η) (hs : Surjective η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a)) {ε : ℝ} (hε : 0 < ε)
    {s : Set ℤ} {O : ℤ → Set X} (hO : ∀ k ∈ s, IsOpen (O k))
    (hsub : ∀ k ∈ s, O k ⊆ η '' Icc (ε * (k - 1)) (ε * k)) : s.PairwiseDisjoint O := by
  have key : ∀ j ∈ s, ∀ k ∈ s, j < k → O j ∩ O k = ∅ := by
    intro j hj k hk hjk
    have h1 : (j : ℝ) + 1 ≤ k := by exact_mod_cast Int.add_one_le_iff.2 hjk
    exact eq_empty_of_isOpen_subset_image_Icc_inter hc hs hμ
      (mul_lt_mul_of_pos_left (by linarith) hε)
      (mul_le_mul_of_nonneg_left (by linarith) hε.le)
      (mul_lt_mul_of_pos_left (by linarith) hε) ((hO j hj).inter (hO k hk))
      (inter_subset_inter (hsub j hj) (hsub k hk))
  intro j hj k hk hjk
  show Disjoint (O j) (O k)
  rw [disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j hj k hk h
  · rw [inter_comm]; exact key k hk j hj h

end LatticeProb
