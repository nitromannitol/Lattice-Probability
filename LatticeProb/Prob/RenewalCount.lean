import Mathlib

/-!
# Counting the hits of an adapted sequence of events

Let `F` be a filtration of a probability space `(Ω, P)` and let `H k ∈ F k` be events ("hits").
Suppose that for every `k ∈ [1, n]` and every `A ∈ F k`, the event `A` is followed by a hit at
some time `j ≥ k + 2` with conditional probability at most `q`:
`P (A ∩ ⋃_{j ∈ [k + 2, n]} H j) ≤ q * P A`.
Then the number of hits `#{k ∈ [1, n] : ω ∈ H k}` has the geometric tail
`P (#hits ≥ 2 j + 1) ≤ q ^ j`.

Proof.  Let `D i k = H k ∩ {exactly i hits before k}`, the event that `k` is the `(i + 1)`-th hit;
it lies in `F k`, and the `D i k` are pairwise disjoint in `k` with union `{#hits ≥ i + 1}`.
If there are at least `i + 3` hits then, at the `(i + 1)`-th hit `k`, two further hits follow, the
later of which is at a time `≥ k + 2`.  Hence `P (#hits ≥ i + 3) ≤ q * P (#hits ≥ i + 1)`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*}

open Classical in
/-- The number of indices `k ∈ [a, b]` with `ω ∈ H k`. -/
noncomputable def hitCount (H : ℕ → Set Ω) (a b : ℕ) (ω : Ω) : ℕ :=
  ((Finset.Icc a b).filter fun k => ω ∈ H k).card

lemma hitCount_zero (H : ℕ → Set Ω) (ω : Ω) : hitCount H 1 0 ω = 0 := by
  simp [hitCount]

lemma hitCount_succ_of_mem (H : ℕ → Set Ω) (ω : Ω) (m : ℕ) (h : ω ∈ H (m + 1)) :
    hitCount H 1 (m + 1) ω = hitCount H 1 m ω + 1 := by
  classical
  unfold hitCount
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  simp [h]

lemma hitCount_succ_of_notMem (H : ℕ → Set Ω) (ω : Ω) (m : ℕ) (h : ω ∉ H (m + 1)) :
    hitCount H 1 (m + 1) ω = hitCount H 1 m ω := by
  classical
  unfold hitCount
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
  simp [h]

open Classical in
lemma hitCount_mono (H : ℕ → Set Ω) (ω : Ω) {m m' : ℕ} (h : m ≤ m') :
    hitCount H 1 m ω ≤ hitCount H 1 m' ω :=
  Finset.card_le_card (Finset.monotone_filter_left _ (Finset.Icc_subset_Icc_right h))

lemma measurableSet_hitCount_eq {m : MeasurableSpace Ω} (H : ℕ → Set Ω) (a b : ℕ)
    (hH : ∀ l ∈ Finset.Icc a b, MeasurableSet[m] (H l)) (i : ℕ) :
    MeasurableSet[m] {ω | hitCount H a b ω = i} := by
  classical
  have hmeas : Measurable fun ω => hitCount H a b ω := by
    have : (fun ω => hitCount H a b ω) = fun ω => ∑ l ∈ Finset.Icc a b, if ω ∈ H l then 1 else 0 := by
      funext ω
      simp only [hitCount, Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ fun l hl => Measurable.ite (hH l hl) measurable_const measurable_const
  exact hmeas (measurableSet_singleton i)

/-- The event that `k` is the `(i + 1)`-th hit. -/
def hitEvent (H : ℕ → Set Ω) (i k : ℕ) : Set Ω :=
  H k ∩ {ω | hitCount H 1 (k - 1) ω = i}

lemma measurableSet_hitEvent (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (H : ℕ → Set Ω)
    (hH : ∀ k, MeasurableSet[F k] (H k)) (i k : ℕ) : MeasurableSet[F k] (hitEvent H i k) :=
  (hH k).inter (measurableSet_hitCount_eq (m := F k) H 1 (k - 1)
    (fun l hl => hF (by have := (Finset.mem_Icc.1 hl).2; omega) _ (hH l)) i)

lemma iUnion_hitEvent (H : ℕ → Set Ω) (n i : ℕ) :
    {ω | i + 1 ≤ hitCount H 1 n ω} = ⋃ k ∈ Finset.Icc 1 n, hitEvent H i k := by
  ext ω
  simp only [Set.mem_iUnion, hitEvent, Set.mem_inter_iff, Finset.mem_Icc, exists_prop,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    have hex : ∃ m, i + 1 ≤ hitCount H 1 m ω := ⟨n, h⟩
    have hk : i + 1 ≤ hitCount H 1 (Nat.find hex) ω := Nat.find_spec hex
    have hkn : Nat.find hex ≤ n := Nat.find_min' hex h
    have hk0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, hitCount_zero] at hk
      omega
    obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hmin : ¬ i + 1 ≤ hitCount H 1 k' ω := Nat.find_min hex (by omega)
    rw [hk'] at hk
    by_cases hn : ω ∈ H (k' + 1)
    · rw [hitCount_succ_of_mem H ω k' hn] at hk
      exact ⟨k' + 1, ⟨by omega, by omega⟩, hn, by rw [Nat.add_sub_cancel]; omega⟩
    · rw [hitCount_succ_of_notMem H ω k' hn] at hk
      omega
  · rintro ⟨k, ⟨hk1, hkn⟩, hkH, hc⟩
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have := hitCount_mono H ω hkn
    rw [hitCount_succ_of_mem H ω k' hkH] at this
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hc
    omega

lemma pairwiseDisjoint_hitEvent (H : ℕ → Set Ω) (n i : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ) (hitEvent H i) := by
  intro k hk k' hk' hne
  wlog hlt : k < k' generalizing k k'
  · exact (this hk' hk hne.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)).symm
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨hkH, hkc⟩ ⟨_, hk'c⟩
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 (Finset.mem_coe.1 hk)).1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h1 := hitCount_mono H ω (show m + 1 ≤ k' - 1 by omega)
  simp only [Set.mem_ofPred_eq] at hkc
  have hkc' : hitCount H 1 m ω = i := by simpa using hkc
  rw [hitCount_succ_of_mem H ω m hkH, hkc'] at h1
  have hk'c' : hitCount H 1 (k' - 1) ω = i := hk'c
  omega

lemma subset_iUnion_hitEvent_inter (H : ℕ → Set Ω) (n i : ℕ) :
    {ω | i + 3 ≤ hitCount H 1 n ω} ⊆
      ⋃ k ∈ Finset.Icc 1 n, (hitEvent H i k ∩ ⋃ j ∈ Finset.Icc (k + 2) n, H j) := by
  classical
  intro ω hω
  have hω' : ω ∈ {ω | i + 1 ≤ hitCount H 1 n ω} := by
    simp only [Set.mem_ofPred_eq] at hω ⊢
    omega
  rw [iUnion_hitEvent] at hω'
  simp only [Set.mem_iUnion, exists_prop] at hω' ⊢
  obtain ⟨k, hk, hkE⟩ := hω'
  refine ⟨k, hk, hkE, ?_⟩
  by_contra hno
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and] at hno
  obtain ⟨hkH, hkc⟩ := hkE
  simp only [Set.mem_ofPred_eq] at hkc hω
  have hsub : (Finset.Icc 1 n).filter (fun l => ω ∈ H l) ⊆
      ((Finset.Icc 1 (k - 1)).filter (fun l => ω ∈ H l)) ∪ {k, k + 1} := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hxn⟩, hxH⟩ := hx
    by_cases hxk : x ≤ k - 1
    · exact Finset.mem_union_left _ (by simp [Finset.mem_Icc]; exact ⟨⟨hx1, hxk⟩, hxH⟩)
    · by_cases hx2 : k + 2 ≤ x
      · exact absurd hxH (hno x (Finset.mem_Icc.2 ⟨hx2, hxn⟩))
      · apply Finset.mem_union_right
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
  have hcard := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.Icc 1 (k - 1)).filter (fun l => ω ∈ H l)) {k, k + 1}
  have h3 : ({k, k + 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  have h4 : hitCount H 1 (k - 1) ω = ((Finset.Icc 1 (k - 1)).filter (fun l => ω ∈ H l)).card := rfl
  have h5 : hitCount H 1 n ω = ((Finset.Icc 1 n).filter (fun l => ω ∈ H l)).card := rfl
  omega

open Classical in
/-- **Geometric tail for the number of hits.**  Let `F` be a filtration and `H k ∈ F k` events.
If, for every `k ∈ [1, n]` and `A ∈ F k`, `P (A ∩ ⋃_{j ∈ [k + 2, n]} H j) ≤ q * P A`, then
`P (#{k ∈ [1, n] : ω ∈ H k} ≥ 2 j + 1) ≤ q ^ j`. -/
theorem measure_two_mul_add_one_le_card_hits_le {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (F : ℕ → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ k, F k ≤ m0) (H : ℕ → Set Ω) (hH : ∀ k, MeasurableSet[F k] (H k)) (n : ℕ)
    {q : ℝ≥0∞}
    (hesc : ∀ k ∈ Finset.Icc 1 n, ∀ A : Set Ω, MeasurableSet[F k] A →
      P (A ∩ ⋃ j ∈ Finset.Icc (k + 2) n, H j) ≤ q * P A) (j : ℕ) :
    P {ω | 2 * j + 1 ≤ ((Finset.Icc 1 n).filter fun k => ω ∈ H k).card} ≤ q ^ j := by
  have step : ∀ i, P {ω | i + 3 ≤ hitCount H 1 n ω} ≤ q * P {ω | i + 1 ≤ hitCount H 1 n ω} := by
    intro i
    calc P {ω | i + 3 ≤ hitCount H 1 n ω}
        ≤ P (⋃ k ∈ Finset.Icc 1 n, (hitEvent H i k ∩ ⋃ j ∈ Finset.Icc (k + 2) n, H j)) :=
          measure_mono (subset_iUnion_hitEvent_inter H n i)
      _ ≤ ∑ k ∈ Finset.Icc 1 n, P (hitEvent H i k ∩ ⋃ j ∈ Finset.Icc (k + 2) n, H j) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 n, q * P (hitEvent H i k) :=
          Finset.sum_le_sum fun k hk => hesc k hk _ (measurableSet_hitEvent F hF H hH i k)
      _ = q * ∑ k ∈ Finset.Icc 1 n, P (hitEvent H i k) := by rw [Finset.mul_sum]
      _ = q * P (⋃ k ∈ Finset.Icc 1 n, hitEvent H i k) := by
          rw [measure_biUnion_finset (pairwiseDisjoint_hitEvent H n i)
            fun k _ => hle k _ (measurableSet_hitEvent F hF H hH i k)]
      _ = q * P {ω | i + 1 ≤ hitCount H 1 n ω} := by rw [iUnion_hitEvent]
  have key : ∀ j : ℕ, P {ω | 2 * j + 1 ≤ hitCount H 1 n ω} ≤ q ^ j := by
    intro j
    induction j with
    | zero => simpa using prob_le_one
    | succ j ih =>
      have h := step (2 * j)
      have e : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
      rw [e, pow_succ']
      exact h.trans (by gcongr)
  exact key j

end LatticeProb
