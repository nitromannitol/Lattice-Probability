import LatticeProb.Prob.InducedMap.RetTimeMeasurability

/-!
# The tower (Kakutani skyscraper) computation

For `B ⊆ A` put `retSet T A B n = {x | T^[n] x ∈ B ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A}` and
`avoidSet T A B n = {x | T^[n] x ∈ B ∧ ∀ j < n, T^[j] x ∉ A}` (so `avoidSet T A B 0 = B`).
Splitting `T⁻¹ (avoidSet A B n)` according to whether `x ∈ A` gives a recursion for the measure
of `avoidSet A B n`, which telescopes to `μ B = ∑' k, μ (A ∩ retSet T A B (k + 1))` once the tail
`μ (avoidSet A B n)` is shown to vanish.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Both `retSet T A B n` and `avoidSet T A B n` are measurable. -/
theorem measurableSet_retSet_avoidSet {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (retSet T A B n) ∧ MeasurableSet (avoidSet T A B n) := by
  refine ⟨?_, ?_⟩
  · show MeasurableSet {x : Ω | T^[n] x ∈ B ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A}
    rw [setOf_and]
    refine MeasurableSet.inter (hB.preimage (hT.iterate n)) ?_
    rw [setOf_forall]
    exact MeasurableSet.iInter fun j => by
      by_cases hj : 0 < j ∧ j < n
      · convert (hA.preimage (hT.iterate j)).compl using 1
        ext x; simp only [Set.mem_setOf_eq]; exact ⟨fun hf => hf hj.1 hj.2, fun hf _ _ => hf⟩
      · convert MeasurableSet.univ using 1
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h1 h2 => absurd ⟨h1, h2⟩ hj
  · show MeasurableSet {x : Ω | T^[n] x ∈ B ∧ ∀ j, j < n → T^[j] x ∉ A}
    rw [setOf_and]
    refine MeasurableSet.inter (hB.preimage (hT.iterate n)) ?_
    rw [setOf_forall]
    exact MeasurableSet.iInter fun j => by
      by_cases hj : j < n
      · convert (hA.preimage (hT.iterate j)).compl using 1
        ext x; simp only [Set.mem_setOf_eq]; exact ⟨fun hf => hf hj, fun hf _ => hf⟩
      · convert MeasurableSet.univ using 1
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h1 => absurd h1 hj

omit [MeasurableSpace Ω] in
/-- Restate `T^[j + 1] x = T^[j] (T x)` locally for the rewrites below. -/
private theorem iterate_succ_apply_shift (T : Ω → Ω) (x : Ω) (j : ℕ) :
    T^[j + 1] x = T^[j] (T x) := Function.iterate_succ_apply T j x

omit [MeasurableSpace Ω] in
/-- Avoidance of `A` by `T^[·] (T x)` below `n` is the same as avoidance by `T^[·] x` at
positive times below `n + 1`. -/
private theorem forall_lt_iterate_comp_notMem_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) (n : ℕ) :
    (∀ j, j < n → T^[j] (T x) ∉ A) ↔ (∀ j, 0 < j → j < n + 1 → T^[j] x ∉ A) := by
  constructor
  · intro h j hj0 hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj0)
    have h1 : T^[k.succ] x ∉ A := h k (by omega)
    rw [Function.iterate_succ_apply] at h1
    exact h1
  · intro h j hj
    have h1 : T^[j.succ] x ∉ A := h (j + 1) (by omega) (by omega)
    rw [Function.iterate_succ_apply] at h1
    exact h1

omit [MeasurableSpace Ω] in
/-- Avoidance of `A` by `T^[·] x` at every time below `n + 1` splits into `x ∉ A` together with
avoidance at every positive time below `n + 1`. -/
private theorem forall_lt_succ_iterate_notMem_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) (n : ℕ) :
    (∀ j, j < n + 1 → T^[j] x ∉ A) ↔
      (x ∉ A ∧ ∀ j, 0 < j → j < n + 1 → T^[j] x ∉ A) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h 0 (by omega)
    · intro j hj0 hj
      exact h j hj
  · rintro ⟨h0, h⟩ j hj
    rcases Nat.eq_zero_or_pos j with hz | hj0
    · subst hz
      simpa using h0
    · exact h j hj0 hj

omit [MeasurableSpace Ω] in
/-- `T⁻¹ (avoidSet T A B n)` splits into the disjoint union of `A ∩ retSet T A B (n + 1)` and
`avoidSet T A B (n + 1)`. -/
private theorem preimage_avoidSet_eq_union (T : Ω → Ω) (A B : Set Ω) (n : ℕ) :
    T ⁻¹' avoidSet T A B n = (A ∩ retSet T A B (n + 1)) ∪ avoidSet T A B (n + 1) := by
  ext x
  simp only [mem_preimage, mem_union, mem_inter_iff, retSet, avoidSet, mem_setOf_eq]
  rw [iterate_succ_apply_shift]
  rw [forall_lt_iterate_comp_notMem_iff, forall_lt_succ_iterate_notMem_iff]
  by_cases h : x ∈ A <;> simp [h]

omit [MeasurableSpace Ω] in
/-- The two pieces of `preimage_avoidSet_eq_union` are disjoint. -/
private theorem disjoint_inter_retSet_avoidSet (T : Ω → Ω) (A B : Set Ω) (n : ℕ) :
    Disjoint (A ∩ retSet T A B (n + 1)) (avoidSet T A B (n + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hy.2 0 (Nat.zero_lt_succ n) hx.1

/-- Measure-preservation and `preimage_avoidSet_eq_union` give the one-step recursion
`μ (avoidSet T A B n) = μ (A ∩ retSet T A B (n + 1)) + μ (avoidSet T A B (n + 1))`. -/
private theorem measure_avoidSet_eq_add_avoidSet_succ {μ : Measure Ω} {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) :
    μ (avoidSet T A B n) = μ (A ∩ retSet T A B (n + 1)) + μ (avoidSet T A B (n + 1)) := by
  have hB8 : MeasurableSet (avoidSet T A B (n + 1)) :=
    (measurableSet_retSet_avoidSet hT.measurable hA hB (n + 1)).2
  have hBn : MeasurableSet (avoidSet T A B n) :=
    (measurableSet_retSet_avoidSet hT.measurable hA hB n).2
  rw [← hT.measure_preimage hBn.nullMeasurableSet, preimage_avoidSet_eq_union]
  rw [measure_union (disjoint_inter_retSet_avoidSet T A B n) hB8]

/-- Unrolling `measure_avoidSet_eq_add_avoidSet_succ` by induction on `n` gives
`μ B = ∑_{k<n} μ (A ∩ retSet T A B (k + 1)) + μ (avoidSet T A B n)`. -/
private theorem measure_eq_sum_measure_inter_retSet_add_avoidSet {μ : Measure Ω} {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) :
    μ B = (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n) := by
  induction n with
  | zero => simp [avoidSet]
  | succ n ih =>
    have h11 := measure_avoidSet_eq_add_avoidSet_succ hT hA hB n
    rw [Finset.sum_range_succ, ih, h11, add_assoc]

omit [MeasurableSpace Ω] in
/-- The sets `avoidSet T A B n`, `n : ℕ`, are pairwise disjoint (a point of `avoidSet ... m`
lies in `B ⊆ A`, contradicting avoidance of `A` at time `m` recorded by `avoidSet ... n` for
`n ≠ m`). -/
private theorem pairwise_disjoint_avoidSet (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (avoidSet T A B)) := by
  intro m n hmn
  show Disjoint (avoidSet T A B m) (avoidSet T A B n)
  rw [Set.disjoint_left]
  intro x hm hn
  simp only [avoidSet, mem_setOf_eq] at hm hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hn.2 m hlt (hBA hm.1)
  · exact hm.2 n hgt (hBA hn.1)

/-- The tail measure `μ (avoidSet T A B n)` tends to `0` as `n → ∞`, since the `avoidSet T A B n`
are pairwise disjoint subsets of the finite-measure space. -/
private theorem tendsto_measure_avoidSet_atTop_nhds_zero {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : Tendsto (fun n => μ (avoidSet T A B n)) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (avoidSet T A B n) :=
    fun n => (measurableSet_retSet_avoidSet hT hA hB n).2
  have hdisj : Pairwise (Function.onFun Disjoint (avoidSet T A B)) :=
    pairwise_disjoint_avoidSet T hBA
  have hle : (∑' n : ℕ, μ (avoidSet T A B n)) ≤ μ Set.univ :=
    le_trans (MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint μ hmeas hdisj)
      (measure_mono (Set.subset_univ _))
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ) hle

/-- Letting `n → ∞` in `measure_eq_sum_measure_inter_retSet_add_avoidSet` and using
`tendsto_measure_avoidSet_atTop_nhds_zero` gives `μ B = ∑' k, μ (A ∩ retSet T A B (k + 1))`. -/
theorem measure_eq_tsum_measure_inter_retSet {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : μ B = ∑' k : ℕ, μ (A ∩ retSet T A B (k + 1)) := by
  have hsum : Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n))
      atTop (𝓝 ((∑' k : ℕ, μ (A ∩ retSet T A B (k + 1))) + 0)) :=
    (ENNReal.tendsto_nat_tsum (fun k => μ (A ∩ retSet T A B (k + 1)))).add
      (tendsto_measure_avoidSet_atTop_nhds_zero (μ := μ) (T := T) (A := A) (B := B)
        hT.measurable hA hB hBA)
  have hconst : Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n))
      atTop (𝓝 (μ B)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => μ B) atTop (𝓝 (μ B))).congr'
      (Filter.Eventually.of_forall
        fun n => measure_eq_sum_measure_inter_retSet_add_avoidSet hT hA hB n)
  have hfin := tendsto_nhds_unique hconst hsum
  simpa only [add_zero] using hfin

end LatticeProb
