/-
Kac's lemma.

For `T` preserving a probability measure `μ` and a measurable `A`, with `retTime T A` the first
return time to `A` (`LatticeProb.Prob.ReturnTime`):
  `∫⁻ x in A, retTime T A x ∂μ = μ {x | ∃ n, T^[n] x ∈ A}`             (no ergodicity needed)
and for ergodic `T` with `μ A ≠ 0` the right side is `1` (`kac`). In particular `retTime T A` is
integrable on `A` (`kac_integrable`, which needs no ergodicity: the integral is `≤ 1`,
`kac_le`).

Route (tower identity). Let `Y n = avoidSet T A A n` be the points whose first entrance to `A`
(time `≥ 0`) is at time `n`. Splitting `T⁻¹ (Y n)` according to whether `x ∈ A` gives the
recursion `μ (Y n) = μ (A ∩ retSet T A A (n+1)) + μ (Y (n+1))`, and the `Y n` are pairwise
disjoint with finite total measure, so `μ (Y n) → 0`. Since `A ∩ retSet T A A (n+1) = A ∩
{retTime = n+1}`, telescoping gives `μ (Y n) = ∑' k, μ (A ∩ {retTime = n+1+k}) = μ (A ∩
{n < retTime})`. Summing over `n` (a layer-cake identity for an `ℕ`-valued function,
`∑' n, 1{n < r} = r`):
  `∫⁻_A retTime = ∑' n, μ (A ∩ {n < retTime}) = ∑' n, μ (Y n) = μ (⋃ n, Y n)`,
and `⋃ n, Y n = {x | ∃ n, T^[n] x ∈ A}` (first entrance, by `Nat.find`). That set `U` satisfies
`T⁻¹ U ⊆ U` and `A ⊆ U`, so ergodicity (`Ergodic.ae_empty_or_univ_of_preimage_ae_le`) and
`μ A ≠ 0` force `μ U = 1`.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import Mathlib
import LatticeProb.Prob.ReturnTime

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Restated from the induced-map formalization -/

omit [MeasurableSpace Ω] in
/-- For `0 < n`, `retTime T A x = n` iff `T^[n] x ∈ A` and no earlier positive iterate does. -/
private theorem retTime_eq_iff' (T : Ω → Ω) (A : Set Ω) (x : Ω) {n : ℕ} (hn : 0 < n) :
    retTime T A x = n ↔ T^[n] x ∈ A ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A := by
  classical
  unfold retTime
  by_cases h : ∃ n, 0 < n ∧ T^[n] x ∈ A
  · rw [dif_pos h, Nat.find_eq_iff h]
    constructor
    · intro hp
      exact ⟨hp.1.2, fun j hj hjn hmem => hp.2 j hjn ⟨hj, hmem⟩⟩
    · rintro ⟨hmem, havoid⟩
      exact ⟨⟨hn, hmem⟩, fun j hjn hpj => havoid j hpj.1 hjn hpj.2⟩
  · rw [dif_neg h]
    constructor
    · intro h0; omega
    · rintro ⟨hmem, _⟩
      exact absurd ⟨n, hn, hmem⟩ h

/-- The set of points that have not returned to `A` before time `l` is measurable. -/
private theorem measurableSet_avoidCondition {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω}
    (hT : Measurable T)
    {A : Set Ω} (hA : MeasurableSet A) (l : ℕ) :
    MeasurableSet {x : Ω | ∀ j, 0 < j → j < l → T^[j] x ∉ A} := by
  have hset : {x : Ω | ∀ j, 0 < j → j < l → T^[j] x ∉ A}
      = ⋂ j : ℕ, (((T^[j]) ⁻¹' A)ᶜ ∪ {x : Ω | ¬ (0 < j ∧ j < l)}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_preimage]
    constructor
    · intro h j
      by_cases hj : 0 < j ∧ j < l
      · exact Or.inl (h j hj.1 hj.2)
      · exact Or.inr hj
    · rintro h j hj hjl
      rcases h j with hc | hnc
      · exact hc
      · exact absurd ⟨hj, hjl⟩ hnc
  rw [hset]
  refine MeasurableSet.iInter fun j => MeasurableSet.union ((hT.iterate j) hA).compl ?_
  by_cases h : 0 < j ∧ j < l
  · have : {x : Ω | ¬ (0 < j ∧ j < l)} = (∅ : Set Ω) := by
      ext x; simp [h]
    rw [this]; exact MeasurableSet.empty
  · have : {x : Ω | ¬ (0 < j ∧ j < l)} = (univ : Set Ω) := by
      ext x; simp [h]
    rw [this]; exact MeasurableSet.univ

/-- Each level set `{retTime T A = n}` is measurable. -/
private theorem measurableSet_retTime_preimage_singleton {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet (retTime T A ⁻¹' {n}) := by
  classical
  cases n with
  | zero =>
    have hset : (retTime T A) ⁻¹' {0} = (⋃ k : ℕ, (T^[k + 1]) ⁻¹' A)ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion]
      unfold retTime
      by_cases h : ∃ n, 0 < n ∧ T^[n] x ∈ A
      · rw [dif_pos h]
        constructor
        · intro hf
          exact absurd hf ((Nat.find_spec h).1).ne'
        · intro hc
          obtain ⟨k, hk, hmem⟩ := h
          exact absurd ⟨k - 1, by rw [Nat.sub_add_cancel hk]; exact hmem⟩ hc
      · rw [dif_neg h]
        constructor
        · intro _ hk
          obtain ⟨k, hk'⟩ := hk
          exact h ⟨k + 1, Nat.succ_pos k, hk'⟩
        · intro _
          rfl
    rw [hset]
    exact MeasurableSet.compl (MeasurableSet.iUnion fun k => (hT.iterate (k + 1)) hA)
  | succ m =>
    have hset : (retTime T A) ⁻¹' {m + 1}
        = {x | T^[m + 1] x ∈ A} ∩ {x | ∀ j, 0 < j → j < m + 1 → T^[j] x ∉ A} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact retTime_eq_iff' T A x (Nat.succ_pos m)
    rw [hset]
    exact MeasurableSet.inter ((hT.iterate (m + 1)) hA) (measurableSet_avoidCondition hT hA (m + 1))

/-- `retTime T A` is measurable. -/
private theorem measurable_retTime' {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    Measurable (retTime T A) := by
  exact measurable_to_countable' fun n => measurableSet_retTime_preimage_singleton hT hA n

/-- `retSet T A B n` and `avoidSet T A B n` are measurable. -/
private theorem measurableSet_retSet_and_avoidSet {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω}
    (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (retSet T A B n) ∧ MeasurableSet (avoidSet T A B n) := by
  constructor
  · rw [show retSet T A B n = (T^[n]) ⁻¹' B ∩
        Set.iInter (fun k : {j : ℕ // 0 < j ∧ j < n} => (T^[k.1]) ⁻¹' Aᶜ) from by
      ext x
      simp only [retSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
        Set.mem_compl_iff]
      exact ⟨fun h => ⟨h.1, fun k => h.2 k.1 k.2.1 k.2.2⟩,
        fun h => ⟨h.1, fun j hj1 hj2 => h.2 ⟨j, hj1, hj2⟩⟩⟩]
    exact (hT.iterate n hB).inter (MeasurableSet.iInter fun k => (hT.iterate k.1) hA.compl)
  · rw [show avoidSet T A B n = (T^[n]) ⁻¹' B ∩
        Set.iInter (fun k : Fin n => (T^[k.1]) ⁻¹' Aᶜ) from by
      ext x
      simp only [avoidSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
        Set.mem_compl_iff]
      exact ⟨fun h => ⟨h.1, fun k => h.2 k.1 k.2⟩,
        fun h => ⟨h.1, fun j hj => h.2 ⟨j, hj⟩⟩⟩]
    exact (hT.iterate n hB).inter (MeasurableSet.iInter fun k => (hT.iterate k.1) hA.compl)

omit [MeasurableSpace Ω] in
/-- `T⁻¹ (avoidSet T A B n)` splits as the return-at-`(n+1)` set union `avoidSet T A B (n+1)`. -/
private theorem preimage_avoidSet_eq_union' (T : Ω → Ω) (A B : Set Ω) (n : ℕ) :
    T ⁻¹' avoidSet T A B n = (A ∩ retSet T A B (n + 1)) ∪ avoidSet T A B (n + 1) := by
  ext x
  simp only [mem_preimage, avoidSet, retSet, mem_setOf_eq, mem_inter_iff, mem_union]
  constructor
  · rintro ⟨hB, hA⟩
    by_cases hx : x ∈ A
    · left
      refine ⟨hx, hB, ?_⟩
      intro j hj0 hjn
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      exact hA m (by omega)
    · right
      refine ⟨hB, ?_⟩
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, Function.iterate_zero_apply]; exact hx
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        exact hA m (by omega)
  · rintro (h | h)
    · obtain ⟨hx, hB, hA⟩ := h
      exact ⟨hB, fun j hj => hA (j + 1) (by omega) (by omega)⟩
    · obtain ⟨hB, hA⟩ := h
      exact ⟨hB, fun j hj => hA (j + 1) (by omega)⟩

/-- `μ (avoidSet T A B n)` splits as a return-at-`(n+1)` measure plus `μ (avoidSet T A B (n+1))`. -/
private theorem measure_avoidSet_eq_add_measure_avoidSet_succ {μ : Measure Ω} {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    μ (avoidSet T A B n) = μ (A ∩ retSet T A B (n + 1)) + μ (avoidSet T A B (n + 1)) := by
  have hm : MeasurableSet (avoidSet T A B n) :=
      (measurableSet_retSet_and_avoidSet hT.measurable hA hB n).2
  have hm' : MeasurableSet (avoidSet T A B (n + 1)) :=
      (measurableSet_retSet_and_avoidSet hT.measurable hA hB (n + 1)).2
  have h1 : μ (T ⁻¹' avoidSet T A B n) = μ (avoidSet T A B n) :=
    hT.measure_preimage hm.nullMeasurableSet
  rw [← h1, preimage_avoidSet_eq_union']
  exact measure_union
    (Set.disjoint_left.mpr fun x hx1 hx2 => hx2.2 0 (Nat.succ_pos n) (by simpa using hx1.1)) hm'

omit [MeasurableSpace Ω] in
/-- The sets `avoidSet T A B n`, for `B ⊆ A`, are pairwise disjoint. -/
private theorem pairwise_disjoint_avoidSet' (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (avoidSet T A B)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hn.2 m h (hBA hm.1)
  · exact hm.2 n h (hBA hn.1)

/-- `μ (avoidSet T A B n) → 0` as `n → ∞`, from finite total measure. -/
private theorem tendsto_measure_avoidSet_atTop_nhds_zero' {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : Measurable T)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    Tendsto (fun n => μ (avoidSet T A B n)) atTop (𝓝 0) := by
  have hdisj : Pairwise (Function.onFun Disjoint (avoidSet T A B)) := pairwise_disjoint_avoidSet' T
      hBA
  have hmeas : ∀ n, MeasurableSet (avoidSet T A B n) := fun n =>
      (measurableSet_retSet_and_avoidSet hT hA hB n).2
  have hUnion : ∑' n, μ (avoidSet T A B n) = μ (⋃ n, avoidSet T A B n) :=
    (measure_iUnion hdisj hmeas).symm
  have hle : μ (⋃ n, avoidSet T A B n) ≤ μ Set.univ := measure_mono (subset_univ _)
  have htop : μ (⋃ n, avoidSet T A B n) ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ _) hle
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by rw [hUnion]; exact htop)

/-! ### The tower identity -/

omit [MeasurableSpace Ω] in
/-- `A ∩ retSet T A A (n+1) = A ∩ {retTime T A = n+1}`. -/
private theorem inter_retSet_succ_eq_inter_retTime_eq (T : Ω → Ω) (A : Set Ω) (n : ℕ) :
    A ∩ retSet T A A (n + 1) = A ∩ {x | retTime T A x = n + 1} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, retSet]
  constructor
  · rintro ⟨ha, hcond⟩
    exact ⟨ha, (retTime_eq_iff' T A x (Nat.succ_pos n)).2 hcond⟩
  · rintro ⟨ha, hr⟩
    exact ⟨ha, (retTime_eq_iff' T A x (Nat.succ_pos n)).1 hr⟩

/-- Telescoping identity for `μ (avoidSet T A A n)` after `m` steps. -/
private theorem measure_avoidSet_eq_sum_add_measure_avoidSet_add {μ : Measure Ω} {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : MeasurableSet A) (n m : ℕ) :
    μ (avoidSet T A A n) =
      (∑ k ∈ Finset.range m, μ (A ∩ {x | retTime T A x = n + 1 + k})) +
        μ (avoidSet T A A (n + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h4 := measure_avoidSet_eq_add_measure_avoidSet_succ hT hA hA (n + m)
    rw [inter_retSet_succ_eq_inter_retTime_eq T A (n + m)] at h4
    rw [show n + m + 1 = n + 1 + m from by omega] at h4
    rw [h4]
    ring

/-- `μ (avoidSet T A A n)` equals the tail sum `∑' k, μ (A ∩ {retTime = n+1+k})`. -/
private theorem measure_avoidSet_eq_tsum_measure_retTime_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (n : ℕ) :
    μ (avoidSet T A A n) = ∑' k : ℕ, μ (A ∩ {x | retTime T A x = n + 1 + k}) := by
  have h2 : ∀ m : ℕ, μ (avoidSet T A A n) =
      (∑ k ∈ Finset.range m, μ (A ∩ {x | retTime T A x = n + 1 + k})) +
        μ (avoidSet T A A (n + m)) :=
    fun m => measure_avoidSet_eq_sum_add_measure_avoidSet_add hT hA n m
  have hsum : Tendsto
      (fun m : ℕ => ∑ k ∈ Finset.range m, μ (A ∩ {x | retTime T A x = n + 1 + k}))
      atTop (𝓝 (∑' k : ℕ, μ (A ∩ {x | retTime T A x = n + 1 + k}))) :=
    ENNReal.tendsto_nat_tsum _
  have hrem : Tendsto (fun m : ℕ => μ (avoidSet T A A (n + m))) atTop (𝓝 (0 : ℝ≥0∞)) :=
    (tendsto_measure_avoidSet_atTop_nhds_zero' hT.measurable hA hA (subset_refl A)).comp
      ((tendsto_add_atTop_nat n).congr (fun m => Nat.add_comm m n))
  have hplus : Tendsto
      (fun m : ℕ => (∑ k ∈ Finset.range m, μ (A ∩ {x | retTime T A x = n + 1 + k})) +
        μ (avoidSet T A A (n + m))) atTop
      (𝓝 ((∑' k : ℕ, μ (A ∩ {x | retTime T A x = n + 1 + k})) + 0)) :=
    hsum.add hrem
  rw [add_zero] at hplus
  have hconst : Tendsto (fun _ : ℕ => μ (avoidSet T A A n)) atTop
      (𝓝 (∑' k : ℕ, μ (A ∩ {x | retTime T A x = n + 1 + k}))) :=
    hplus.congr (fun m => (h2 m).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- The tail sum of `μ (A ∩ {retTime = n+1+k})` equals `μ (A ∩ {n < retTime})`. -/
private theorem tsum_measure_retTime_eq_eq_measure_lt_retTime {μ : Measure Ω} {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (n : ℕ) :
    ∑' k : ℕ, μ (A ∩ {x | retTime T A x = n + 1 + k}) = μ (A ∩ {x | n < retTime T A x}) := by
  have hset : A ∩ {x | n < retTime T A x} = ⋃ k, A ∩ {x | retTime T A x = n + 1 + k} :=
    Set.ext fun x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hxA, hlt⟩
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
        exact ⟨k, hxA, by omega⟩
      · rintro ⟨k, hxA, hk⟩
        exact ⟨hxA, by omega⟩
  have hmeas : ∀ k : ℕ, MeasurableSet (A ∩ {x | retTime T A x = n + 1 + k}) := fun k =>
    hA.inter ((measurable_retTime' hT hA) (measurableSet_singleton (n + 1 + k)))
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => A ∩ {x | retTime T A x = n + 1 + k})
      :=
    fun k l hkl => Set.disjoint_left.mpr (by
      intro x hx hxl
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx hxl
      exact hkl (by omega))
  rw [← measure_iUnion hdisj hmeas]
  exact congrArg μ hset.symm

/-- `(k : ℝ≥0∞)` is the sum over `n` of the indicator of `n < k`. -/
private theorem natCast_eq_tsum_ite_lt (k : ℕ) :
    (k : ℝ≥0∞) = ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) := by
  rw [tsum_eq_sum (s := Finset.range k) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    simp [hn])]
  rw [Finset.sum_boole,
    Finset.filter_true_of_mem (p := fun x => x < k) (fun x hx => by simpa using hx),
    Finset.card_range]

omit [MeasurableSpace Ω] in
/-- `retTime T A x`, cast to `ℝ≥0∞`, is a layer-cake sum of indicators of `{n < retTime}`. -/
private theorem natCast_retTime_eq_tsum_indicator_lt (T : Ω → Ω) (A : Set Ω) (x : Ω) :
    ((retTime T A x : ℕ) : ℝ≥0∞) =
      ∑' n : ℕ, ({y | n < retTime T A y} : Set Ω).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  exact natCast_eq_tsum_ite_lt (retTime T A x)

/-- `∫⁻_A retTime` equals `∑' n, μ (A ∩ {n < retTime})`, by the layer-cake formula. -/
private theorem lintegral_retTime_eq_tsum_measure_lt_retTime {μ : Measure Ω} {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    ∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ (A ∩ {x | n < retTime T A x}) := by
  classical
  rw [lintegral_congr (fun x => natCast_retTime_eq_tsum_indicator_lt T A x)]
  rw [lintegral_tsum]
  · refine tsum_congr (fun n => ?_)
    rw [← lintegral_indicator hA]
    rw [indicator_indicator]
    rw
        [lintegral_indicator_const
        (hA.inter (measurableSet_lt measurable_const (measurable_retTime' hT hA))) 1]
    rw [one_mul]
  · intro n
    exact (measurable_const.indicator
      (measurableSet_lt measurable_const (measurable_retTime' hT hA))).aemeasurable

/-- `∑' n, μ (avoidSet T A A n) = μ (⋃ n, avoidSet T A A n)`, by disjointness. -/
private theorem tsum_measure_avoidSet_eq_measure_iUnion {μ : Measure Ω} {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) :
    ∑' n : ℕ, μ (avoidSet T A A n) = μ (⋃ n, avoidSet T A A n) := by
  exact (measure_iUnion (pairwise_disjoint_avoidSet' T (subset_refl A : A ⊆ A))
    (fun n => (measurableSet_retSet_and_avoidSet hT hA hA n).2)).symm

omit [MeasurableSpace Ω] in
/-- `⋃ n, avoidSet T A A n` is exactly the first-entrance set `{x | ∃ n, T^[n] x ∈ A}`. -/
private theorem iUnion_avoidSet_eq_setOf_exists_mem (T : Ω → Ω) (A : Set Ω) :
    (⋃ n, avoidSet T A A n) = {x | ∃ n, T^[n] x ∈ A} := by
  classical
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · rintro ⟨n, hn⟩
    have h : ∃ m : ℕ, T^[m] x ∈ A := ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find h, ?_⟩
    exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- **The first-return integral identity** (no ergodicity needed): the mean of `retTime T A` on
`A` equals the measure of the whole basin `{x | ∃ n, T^[n] x ∈ A}`. -/
theorem lintegral_retTime_eq_measure_hit {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ = μ {x | ∃ n, T^[n] x ∈ A} := by
  rw [lintegral_retTime_eq_tsum_measure_lt_retTime (μ := μ) hT.measurable hA]
  trans ∑' n : ℕ, μ (avoidSet T A A n)
  · exact (tsum_congr (fun n => (measure_avoidSet_eq_tsum_measure_retTime_eq (μ := μ) hT hA n).trans
      (tsum_measure_retTime_eq_eq_measure_lt_retTime (μ := μ) hT.measurable hA n))).symm
  · rw
      [tsum_measure_avoidSet_eq_measure_iUnion (μ := μ) hT.measurable hA,
      iUnion_avoidSet_eq_setOf_exists_mem]

/-! ### Ergodicity: the orbit of `A` is almost everything -/

/-- The basin `{x | ∃ n, T^[n] x ∈ A}` is measurable, contains `A`, and is forward invariant. -/
private theorem measurableSet_basin_subset_and_forward_invariant {T : Ω → Ω} (hT : Measurable T)
    {A : Set Ω} (hA : MeasurableSet A) :
    MeasurableSet {x | ∃ n, T^[n] x ∈ A} ∧ A ⊆ {x | ∃ n, T^[n] x ∈ A} ∧
      T ⁻¹' {x | ∃ n, T^[n] x ∈ A} ⊆ {x | ∃ n, T^[n] x ∈ A} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [setOf_exists]
    exact MeasurableSet.iUnion fun n => (hT.iterate n) hA
  · intro x hx
    exact ⟨0, by simpa using hx⟩
  · rintro x ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

/-- For ergodic `T` and `μ A ≠ 0`, the basin of `A` has full measure. -/
private theorem measure_basin_eq_one_of_ergodic {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (herg : Ergodic T μ) {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    μ {x | ∃ n, T^[n] x ∈ A} = 1 := by
  obtain ⟨hUm, hAU, hTU⟩ := measurableSet_basin_subset_and_forward_invariant
      herg.toMeasurePreserving.measurable hA
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hUm.nullMeasurableSet hTU.eventuallyLE with h | h
  · exfalso
    have hle : μ A ≤ μ {x | ∃ n, T^[n] x ∈ A} := measure_mono hAU
    rw [measure_congr h, measure_empty] at hle
    exact hA0 (le_antisymm hle bot_le)
  · rw [measure_congr h, measure_univ]

/-! ### Conclusions -/

/-- The return time has mean at most one on `A` (no ergodicity needed). -/
theorem kac_le (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ ≤ 1 := by
  rw [lintegral_retTime_eq_measure_hit hT hA]
  exact prob_le_one

/-- The return time `retTime T A` is integrable on `A` (no ergodicity needed: the integral is
`≤ 1` by `kac_le`). -/
theorem kac_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    Integrable (fun x => (retTime T A x : ℝ)) (μ.restrict A) := by
  have hcast : Measurable fun n : ℕ => ((n : ℕ) : ℝ≥0∞) := measurable_from_nat
  have hm : Measurable fun x => ((retTime T A x : ℕ) : ℝ≥0∞) :=
    hcast.comp (measurable_retTime' hT.measurable hA)
  refine (integrable_toReal_of_lintegral_ne_top hm.aemeasurable ?_ :
    Integrable (fun x => ENNReal.toReal ((retTime T A x : ℕ) : ℝ≥0∞)) (μ.restrict A))
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (kac_le μ T hT hA)

/-- The Bochner integral of `retTime` on `A` is the real part of its `lintegral`. -/
private theorem integral_retTime_eq_toReal_lintegral_retTime (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ x in A, (retTime T A x : ℝ) ∂μ = (∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ).toReal := by
  have hfm : AEMeasurable (fun x => (retTime T A x : ℝ≥0∞)) (μ.restrict A) :=
    ((Measurable.comp measurable_from_nat (measurable_retTime' hT.measurable hA))).aemeasurable
  have hfin : ∀ᵐ x ∂(μ.restrict A), (retTime T A x : ℝ≥0∞) < ∞ :=
    Filter.Eventually.of_forall fun x => ENNReal.natCast_lt_top _
  simpa [ENNReal.toReal_natCast] using integral_toReal hfm hfin

/-- **Kac's lemma.** For ergodic `T` and `μ A ≠ 0`, the return time to `A` has mean one on `A`. -/
theorem kac (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω) (herg : Ergodic T μ)
    {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    ∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ = 1 ∧
      Integrable (fun x => (retTime T A x : ℝ)) (μ.restrict A) ∧
      ∫ x in A, (retTime T A x : ℝ) ∂μ = 1 := by
  have h1 : ∫⁻ x in A, (retTime T A x : ℝ≥0∞) ∂μ = 1 := by
    rw
        [lintegral_retTime_eq_measure_hit herg.toMeasurePreserving hA,
        measure_basin_eq_one_of_ergodic herg hA hA0]
  refine ⟨h1, kac_integrable μ T herg.toMeasurePreserving hA, ?_⟩
  rw
      [integral_retTime_eq_toReal_lintegral_retTime μ T herg.toMeasurePreserving hA, h1,
      ENNReal.toReal_one]

end LatticeProb
