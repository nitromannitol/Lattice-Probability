/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/SkorokhodPartition.lean.
-/
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Finite partitions into small continuity sets

Let `P` be a probability measure on a separable pseudo-metric space `S` whose open sets are
measurable. For every `ε > 0` there is a finite measurable partition `B 0, B 1, …, B k` of `S`
(with `B i = ∅` for `i > k`) such that every boundary `∂ (B i)` is `P`-null, `P (B 0) < ε`, and
`diam (B i) < ε` for every `i ≠ 0`.

Source: Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), proof of Theorem 6.7,
first paragraph (display (6.4)): cover `S` by countably many balls with `P`-null boundary and
radius `< ε / 2`, keep the first `k` of them (total mass `> 1 - ε`) and disjointify. Here the
balls are taken around a dense sequence with radii in `(ε / 4, ε / 2)`, which gives the cover
directly, without a countable subcover argument.
-/

open MeasureTheory Set Metric Filter Topology Function
open scoped ENNReal

namespace LatticeProb.Skorokhod

variable {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S]

/-- The boundary of a union of two `P`-null-boundary sets is `P`-null. -/
lemma measure_frontier_union_null (P : Measure S) {s t : Set S} (hs : P (frontier s) = 0)
    (ht : P (frontier t) = 0) : P (frontier (s ∪ t)) = 0 :=
  measure_mono_null ((frontier_union_subset s t).trans
    (union_subset_union inter_subset_left inter_subset_right)) (measure_union_null hs ht)

/-- The boundary of an intersection of two `P`-null-boundary sets is `P`-null. -/
lemma measure_frontier_inter_null (P : Measure S) {s t : Set S} (hs : P (frontier s) = 0)
    (ht : P (frontier t) = 0) : P (frontier (s ∩ t)) = 0 :=
  measure_mono_null ((frontier_inter_subset s t).trans
    (union_subset_union inter_subset_left inter_subset_right)) (measure_union_null hs ht)

/-- The boundary of the complement of a `P`-null-boundary set is `P`-null. -/
lemma measure_frontier_compl_null (P : Measure S) {s : Set S} (hs : P (frontier s) = 0) :
    P (frontier sᶜ) = 0 := by rwa [frontier_compl]

/-- The boundary of a finite union of `P`-null-boundary sets is `P`-null. -/
lemma measure_frontier_biUnion_range_null (P : Measure S) {A : ℕ → Set S}
    (hA : ∀ j, P (frontier (A j)) = 0) (k : ℕ) :
    P (frontier (⋃ l ∈ Finset.range k, A l)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert]
    exact measure_frontier_union_null P (hA k) ih

/-- **Billingsley (6.4).** A finite partition of `S` into `P`-continuity sets, all but the first
of diameter `< ε`, the first of mass `< ε`. The space is separable and its open sets are
measurable; `P` is a probability measure. -/
theorem exists_skorokhodPartition [OpensMeasurableSpace S] [TopologicalSpace.SeparableSpace S]
    (P : Measure S) [IsProbabilityMeasure P] {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (B : ℕ → Set S), (∀ i, MeasurableSet (B i)) ∧ Pairwise (Disjoint on B) ∧
      (⋃ i, B i) = univ ∧ (∀ i, k < i → B i = ∅) ∧ (∀ i, P (frontier (B i)) = 0) ∧
      P (B 0) < ENNReal.ofReal ε ∧ ∀ i, i ≠ 0 → ∀ x ∈ B i, ∀ y ∈ B i, dist x y < ε := by
  have : Nonempty S := nonempty_of_isProbabilityMeasure P
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq S
  have hr : ∀ j, ∃ r ∈ Ioo (ε / 4) (ε / 2), P (frontier (thickening r {d j})) = 0 :=
    fun j => exists_null_frontier_thickening P {d j} (by linarith)
  choose r hr hrP using hr
  set A : ℕ → Set S := fun j => ball (d j) (r j) with hA_def
  have hA0 : ∀ j, P (frontier (A j)) = 0 := by
    intro j; simpa [A, thickening_singleton] using hrP j
  have hAcov : ∀ x, ∃ j, x ∈ A j := by
    intro x
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hd x (ε / 4) (by linarith)
    exact ⟨j, by simp only [A, mem_ball]; linarith [(hr j).1]⟩
  set C : ℕ → Set S := fun j => ⋃ l ∈ Finset.range j, A l with hC_def
  have hCmeas : ∀ j, MeasurableSet (C j) := fun j =>
    Finset.measurableSet_biUnion _ fun l _ => measurableSet_ball
  have hCmono : Monotone C := fun j j' hjj' =>
    biUnion_subset_biUnion_left (by simpa using Finset.range_mono hjj')
  have hlim : Tendsto (fun j => P (C j)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (s := fun j => (C j)ᶜ)
      (fun j => (hCmeas j).compl.nullMeasurableSet) (fun j j' h => compl_subset_compl.2 (hCmono h))
      ⟨0, measure_ne_top P _⟩
    have h0 : (⋂ j, (C j)ᶜ) = ∅ := by
      ext x
      simp only [mem_iInter, mem_compl_iff, mem_empty_iff_false, iff_false, not_forall, not_not]
      obtain ⟨j, hj⟩ := hAcov x
      exact ⟨j + 1, mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self j)) hj⟩
    rw [h0, measure_empty] at h
    exact h
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  set B : ℕ → Set S := fun i => if i = 0 then (C k)ᶜ else if i ≤ k then A (i - 1) \ C (i - 1)
    else ∅ with hB_def
  have hBsub : ∀ i, i ≠ 0 → B i ⊆ A (i - 1) ∩ (C (i - 1))ᶜ ∧ i ≤ k ∨ B i = ∅ := by
    intro i hi
    by_cases hik : i ≤ k
    · left; simp [B, hi, hik, sdiff_eq]
    · right; simp [B, hi, hik]
  have hAC : ∀ l j, l < j → A l ⊆ C j := fun l j hlj =>
    subset_biUnion_of_mem (u := A) (Finset.mem_range.2 hlj)
  refine ⟨k, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [B]
    split_ifs
    · exact (hCmeas k).compl
    · exact measurableSet_ball.diff (hCmeas _)
    · exact MeasurableSet.empty
  · refine (pairwise_disjoint_on B).2 fun i j hij => ?_
    have hj : j ≠ 0 := by omega
    rcases hBsub j hj with ⟨hBj, hjk⟩ | hBj
    · rw [Set.disjoint_iff]
      intro x ⟨hxi, hxj⟩
      have hxj' := hBj hxj
      by_cases hi : i = 0
      · subst hi
        simp only [B, ↓reduceIte] at hxi
        exact hxi (hAC (j - 1) k (by omega) hxj'.1)
      · rcases hBsub i hi with ⟨hBi, -⟩ | hBi
        · exact hxj'.2 (hAC (i - 1) (j - 1) (by omega) (hBi hxi).1)
        · rw [hBi] at hxi; exact hxi
    · rw [hBj]; exact disjoint_empty _
  · refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ C k
    · classical
      obtain ⟨l, hl, hxl⟩ := mem_iUnion₂.1 hx
      set l₀ := Nat.find (hAcov x)
      have hl₀ : l₀ ≤ l := Nat.find_min' _ hxl
      have hlk : l₀ < k := lt_of_le_of_lt hl₀ (Finset.mem_range.1 hl)
      refine mem_iUnion.2 ⟨l₀ + 1, ?_⟩
      simp only [B, Nat.add_one_ne_zero, ite_false, show l₀ + 1 ≤ k by omega, ite_true,
        Nat.add_sub_cancel]
      refine ⟨Nat.find_spec (hAcov x), ?_⟩
      intro hxC
      obtain ⟨l', hl', hxl'⟩ := mem_iUnion₂.1 hxC
      exact Nat.find_min (hAcov x) (Finset.mem_range.1 hl') hxl'
    · exact mem_iUnion.2 ⟨0, by simpa [B] using hx⟩
  · intro i hi
    simp [B, show i ≠ 0 by omega, show ¬ i ≤ k by omega]
  · intro i
    simp only [B]
    split_ifs
    · exact measure_frontier_compl_null P (measure_frontier_biUnion_range_null P hA0 k)
    · rw [sdiff_eq]
      exact measure_frontier_inter_null P (hA0 _)
        (measure_frontier_compl_null P (measure_frontier_biUnion_range_null P hA0 _))
    · simp
  · simpa [B] using hk
  · intro i hi x hx y hy
    rcases hBsub i hi with ⟨hBi, -⟩ | hBi
    · have hx' := (hBi hx).1
      have hy' := (hBi hy).1
      simp only [A, mem_ball] at hx' hy'
      have := dist_triangle_right x y (d (i - 1))
      linarith [(hr (i - 1)).2]
    · rw [hBi] at hx; exact hx.elim

namespace SkorokhodPartitionExample

-- The hypotheses of `exists_skorokhodPartition` hold on `ℝ` for a Dirac mass at `0`.
example := exists_skorokhodPartition (S := ℝ) (Measure.dirac 0) (ε := 1) one_pos

end SkorokhodPartitionExample

end LatticeProb.Skorokhod
