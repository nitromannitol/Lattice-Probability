/-
The first-return (induced) map.

For `T` preserving a finite measure `μ` and a measurable `A`, `retTime T A x` is the first
`n > 0` with `T^[n] x ∈ A` (and `0` if there is none) and `inducedMap T A x = T^[retTime T A x] x`
is the first-return map (`LatticeProb.Prob.ReturnTime`).  The main theorem `induced_map` gives

* Poincare recurrence: `retTime T A x > 0` for a.e. `x ∈ A`;
* `inducedMap T A` preserves `μ.restrict A` (no hypothesis `μ A > 0`);
* `inducedMap T A` is ergodic for `μ.restrict A` when `T` is ergodic for `μ`.

Route for measure preservation (the tower / Kakutani skyscraper computation).  For `B ⊆ A` put
`F n B = {x | T^[n] x ∈ B ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A}` (`retSet`) and
`H n B = {x | T^[n] x ∈ B ∧ ∀ j < n, T^[j] x ∉ A}` (`avoidSet`, `H 0 B = B`).  Splitting
`T⁻¹ (H n B)` according to `x ∈ A` gives `T⁻¹ (H n B) = (A ∩ F (n+1) B) ∪ H (n+1) B`, disjoint,
so `μ (H n B) = μ (A ∩ F (n+1) B) + μ (H (n+1) B)` and by induction
`μ B = ∑_{k<n} μ (A ∩ F (k+1) B) + μ (H n B)`.  The `H n B` are pairwise disjoint, so
`μ (H n B) → 0` and `μ B = ∑' k, μ (A ∩ F (k+1) B)`; `A ∩ inducedMap⁻¹ B` is the disjoint union
of the `A ∩ F (k+1) B` and the null set `A ∩ {retTime = 0} ∩ B`.

Route for ergodicity.  For `E` with `inducedMap⁻¹ E = E`, the first-entrance set
`entSet T A E = {x | ∃ n, T^[n] x ∈ A ∧ (∀ j < n, T^[j] x ∉ A) ∧ T^[n] x ∈ E}` satisfies
`T⁻¹ entSet =ᵐ[μ] entSet` (exact off `A ∩ {retTime = 0}`), and `entSet ∩ A = E ∩ A`; apply
Mathlib's `QuasiErgodic.aeconst_set₀` to `entSet` and restrict to `A`.

The iterates of the induced map are iterates of `T` along the Birkhoff sums of the return time
(`inducedMap_iterate`), which `LatticeProb.Prob.KingmanLinear` uses.

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/
import Mathlib
import LatticeProb.Prob.ReturnTime

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

-- `retTime`, `inducedMap`, `retSet`, `avoidSet`, `entSet` are now defined once, for both this
-- file and `LatticeProb.Prob.Kac`, in `LatticeProb.Prob.ReturnTime` (imported above).

/-! ### 1. The return time -/

-- Unfold `retTime`; `dif_pos`, `Nat.find_eq_iff`; the `0 < n` from `Nat.find_spec`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_1 (T : Ω → Ω) (A : Set Ω) (x : Ω) {n : ℕ} (hn : 0 < n) :
    retTime T A x = n ↔ T^[n] x ∈ A ∧ ∀ j, 0 < j → j < n → T^[j] x ∉ A := by
  classical
  unfold retTime
  by_cases h : ∃ n, 0 < n ∧ T^[n] x ∈ A
  · rw [dif_pos h]
    constructor
    · intro heq
      refine ⟨?_, fun j hj0 hjn hmem => ?_⟩
      · rw [← heq]; exact (Nat.find_spec h).2
      · have := Nat.find_min' h ⟨hj0, hmem⟩
        omega
    · rintro ⟨hmem, hmin⟩
      exact (Nat.find_eq_iff h).mpr ⟨⟨hn, hmem⟩, fun m hm hpm => hmin m hpm.1 hm hpm.2⟩
  · rw [dif_neg h]
    constructor
    · intro h0; omega
    · rintro ⟨hmem, _⟩
      exact (h ⟨n, hn, hmem⟩).elim


-- Unfold `retTime`; if the `∃` holds, `Nat.find_spec` gives `0 < Nat.find h`; else `dif_neg`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_2 (T : Ω → Ω) (A : Set Ω) (x : Ω) :
    retTime T A x = 0 ↔ ∀ n, 0 < n → T^[n] x ∉ A := by
  classical
  constructor
  · intro h0 n hn hmem
    have h : ∃ m, 0 < m ∧ T^[m] x ∈ A := ⟨n, hn, hmem⟩
    rw [retTime, dif_pos h] at h0
    have := (Nat.find_spec h).1
    omega
  · intro hA
    rw [retTime]
    exact dif_neg (by rintro ⟨n, hn, hmem⟩; exact hA n hn hmem)


-- `retTime ≠ 0` gives the `∃` (by `aux_induced_2`), and `Nat.find_spec` lands in `A`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_3 (T : Ω → Ω) (A : Set Ω) (x : Ω) (hx : retTime T A x ≠ 0) :
    inducedMap T A x ∈ A := by
  have hpos : 0 < retTime T A x := Nat.pos_of_ne_zero hx
  have h := (aux_induced_1 T A x hpos).mp rfl
  simpa [inducedMap] using h.1


-- `hA.preimage (hT.iterate n)` (`Measurable.iterate`).
private theorem aux_induced_4 {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    (n : ℕ) : MeasurableSet {x | T^[n] x ∈ A} := by
  exact hA.preimage (hT.iterate n)


-- Per `m`, case on `0 < m` (`Nat.eq_zero_or_pos`): `m = 0` makes the implication vacuous, so the
-- set is `univ` (`MeasurableSet.univ`); `0 < m` reduces it to `{x | T^[m] x ∉ A}`, the complement
-- of `aux_induced_4` (`MeasurableSet.compl`).  Then `MeasurableSet.iInter` over `m : ℕ`
-- (`Set.setOf_forall` to see the set as `⋂ m, {x | 0 < m → T^[m] x ∉ A}`).
private theorem aux_aux_induced_5_1 (T : Ω → Ω) (hT : Measurable T) (A : Set Ω) (hA : MeasurableSet A) :
    MeasurableSet {x : Ω | ∀ m, 0 < m → T^[m] x ∉ A} := by
  rw [Set.setOf_forall]
  refine MeasurableSet.iInter (fun m => ?_)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [show {x : Ω | 0 < m → T^[m] x ∉ A} = {x : Ω | T^[m] x ∉ A} from
      Set.ext (fun x => by simp [hm])]
    exact (hA.preimage (hT.iterate m)).compl

-- Same shape as `aux_aux_induced_5_1` with the extra bound `j < n` on the quantifier: per `j`,
-- case on `0 < j ∧ j < n` (`Classical.em`, or `Nat.lt_or_ge`) to reduce the set to `univ` or to
-- the complement of `aux_induced_4`, then `MeasurableSet.iInter` over `j : ℕ`.
private theorem aux_aux_induced_5_2 (T : Ω → Ω) (hT : Measurable T) (A : Set Ω) (hA : MeasurableSet A)
    (n : ℕ) : MeasurableSet {x : Ω | ∀ j, 0 < j → j < n → T^[j] x ∉ A} := by
  rw [Set.setOf_forall]
  refine MeasurableSet.iInter (fun j => ?_)
  by_cases hj : 0 < j ∧ j < n
  · rw [show {x : Ω | 0 < j → j < n → T^[j] x ∉ A} = {x : Ω | T^[j] x ∉ A} from
      Set.ext (fun x => by simp [hj])]
    exact (hA.preimage (hT.iterate j)).compl
  · rw [show {x : Ω | 0 < j → j < n → T^[j] x ∉ A} = Set.univ from
      Set.ext (fun x => by
        simp only [Set.mem_setOf_eq, Set.mem_univ]
        exact ⟨fun _ => trivial, fun _ h1 h2 => absurd ⟨h1, h2⟩ hj⟩)]
    exact MeasurableSet.univ

-- Case `n = 0`: `aux_induced_2` rewrites the set as the one in `aux_aux_induced_5_1`.
-- Case `0 < n`: `aux_induced_1` rewrites it as the intersection of `aux_induced_4` (for `T^[n]`)
-- with the set in `aux_aux_induced_5_2`; `MeasurableSet.inter`.
private theorem aux_induced_5 {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    (n : ℕ) : MeasurableSet {x | retTime T A x = n} := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hset : {x : Ω | retTime T A x = 0} = {x : Ω | ∀ m, 0 < m → T^[m] x ∉ A} := by
      ext x; exact aux_induced_2 T A x
    rw [hset]
    exact aux_aux_induced_5_1 T hT A hA
  · have hset : {x : Ω | retTime T A x = n} =
        {x : Ω | T^[n] x ∈ A} ∩ {x : Ω | ∀ j, 0 < j → j < n → T^[j] x ∉ A} := by
      ext x; exact aux_induced_1 T A x hn
    rw [hset]
    exact (aux_induced_4 hT hA n).inter (aux_aux_induced_5_2 T hT A hA n)

-- `measurable_to_countable'` with `aux_induced_5`.
theorem measurable_retTime {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (retTime T A) := by
  exact measurable_to_countable' fun n => aux_induced_5 hT hA n


-- `measurable_from_prod_countable_left (fun n => hT.iterate n)` gives measurability of
-- `p : Ω × ℕ ↦ T^[p.2] p.1`; compose with `measurable_id.prodMk (measurable_retTime hT hA)`
-- (same shape as Mathlib's proof of `Measurable.find`).
theorem measurable_inducedMap {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (inducedMap T A) := by
  have h1 : Measurable (fun p : Ω × ℕ => T^[p.2] p.1) :=
    measurable_from_prod_countable_left (fun n => hT.iterate n)
  have h2 : Measurable (fun x : Ω => (x, retTime T A x)) :=
    measurable_id.prodMk (measurable_retTime hT hA)
  exact h1.comp h2


/-! ### 2. The tower computation -/

-- `MeasurableSet.inter` of `aux_induced_4` with `MeasurableSet.iInter` over `j` of the
-- implication sets (complements of `aux_induced_4`); same for `avoidSet`.
private theorem aux_induced_8 {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (n : ℕ) :
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


-- `ext x`; unfold; `Function.iterate_succ_apply` (`T^[n+1] x = T^[n] (T x)`).  `x ∈ A`:
-- avoidance of `A` by `T^[j+1] x`, `j < n`, is avoidance at times `0 < j < n+1`.  `x ∉ A`: it is
-- avoidance at all times `j < n+1` (case `j = 0` is `x ∉ A`).
omit [MeasurableSpace Ω] in
private theorem aux_shift_iter (T : Ω → Ω) (x : Ω) (j : ℕ) :
    T^[j + 1] x = T^[j] (T x) := Function.iterate_succ_apply T j x

omit [MeasurableSpace Ω] in
private theorem aux_forall_shift (T : Ω → Ω) (A : Set Ω) (x : Ω) (n : ℕ) :
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
private theorem aux_forall_split (T : Ω → Ω) (A : Set Ω) (x : Ω) (n : ℕ) :
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
private theorem aux_induced_9 (T : Ω → Ω) (A B : Set Ω) (n : ℕ) :
    T ⁻¹' avoidSet T A B n = (A ∩ retSet T A B (n + 1)) ∪ avoidSet T A B (n + 1) := by
  ext x
  simp only [mem_preimage, mem_union, mem_inter_iff, retSet, avoidSet, mem_setOf_eq]
  rw [aux_shift_iter]
  rw [aux_forall_shift, aux_forall_split]
  by_cases h : x ∈ A <;> simp [h]


-- `Set.disjoint_left`: a point of `avoidSet … (n+1)` is not in `A` (take `j = 0`).
omit [MeasurableSpace Ω] in
private theorem aux_induced_10 (T : Ω → Ω) (A B : Set Ω) (n : ℕ) :
    Disjoint (A ∩ retSet T A B (n + 1)) (avoidSet T A B (n + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hy.2 0 (Nat.zero_lt_succ n) hx.1


-- `hT.measure_preimage` (needs `NullMeasurableSet`, from `aux_induced_8`), rewrite with
-- `aux_induced_9`, then `measure_union aux_induced_10 (…)`.
private theorem aux_induced_11 {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    μ (avoidSet T A B n) = μ (A ∩ retSet T A B (n + 1)) + μ (avoidSet T A B (n + 1)) := by
  have hB8 : MeasurableSet (avoidSet T A B (n + 1)) := (aux_induced_8 hT.measurable hA hB (n + 1)).2
  have hBn : MeasurableSet (avoidSet T A B n) := (aux_induced_8 hT.measurable hA hB n).2
  rw [← hT.measure_preimage hBn.nullMeasurableSet, aux_induced_9]
  rw [measure_union (aux_induced_10 T A B n) hB8]


-- Induction on `n`.  Base: `avoidSet T A B 0 = B` (`simp [avoidSet]`).  Step: `aux_induced_11`,
-- `Finset.sum_range_succ`, `add_assoc`.
private theorem aux_induced_12 {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    μ B = (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n) := by
  induction n with
  | zero => simp [avoidSet]
  | succ n ih =>
    have h11 := aux_induced_11 hT hA hB n
    rw [Finset.sum_range_succ, ih, h11, add_assoc]


-- `Pairwise (Disjoint on …)`: for `m < n`, a point of `avoidSet … n` has `T^[m] x ∉ A`, while a
-- point of `avoidSet … m` has `T^[m] x ∈ B ⊆ A`.  Use `Pairwise.on`/`pairwise_disjoint_on` and
-- `lt_or_gt_of_ne`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_13 (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (avoidSet T A B)) := by
  intro m n hmn
  show Disjoint (avoidSet T A B m) (avoidSet T A B n)
  rw [Set.disjoint_left]
  intro x hm hn
  simp only [avoidSet, mem_setOf_eq] at hm hn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hn.2 m hlt (hBA hm.1)
  · exact hm.2 n hgt (hBA hn.1)


-- `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`; the tsum is `≤ μ (⋃ n, avoidSet …)` by
-- `tsum_meas_le_meas_iUnion_of_disjoint` (with `aux_induced_8`, `aux_induced_13`), which is
-- `≤ μ univ < ∞` (`measure_ne_top`).
private theorem aux_induced_14 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (hT : Measurable T)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    Tendsto (fun n => μ (avoidSet T A B n)) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (avoidSet T A B n) := fun n => (aux_induced_8 hT hA hB n).2
  have hdisj : Pairwise (Function.onFun Disjoint (avoidSet T A B)) := aux_induced_13 T hBA
  have hle : (∑' n : ℕ, μ (avoidSet T A B n)) ≤ μ Set.univ :=
    le_trans (MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint μ hmeas hdisj)
      (measure_mono (Set.subset_univ _))
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ) hle


-- The partial sums tend to `μ B` by `aux_induced_12` and `aux_induced_14`
-- (`μ B - μ (avoidSet …) `, or `tendsto_nhds_unique` with `ENNReal.tendsto_nat_tsum` plus
-- `Tendsto.add`); conclude with `tendsto_nhds_unique`.
private theorem aux_induced_15 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : μ B = ∑' k : ℕ, μ (A ∩ retSet T A B (k + 1)) := by
  have hsum : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n)) atTop (𝓝 ((∑' k : ℕ, μ (A ∩ retSet T A B (k + 1))) + 0)) := (ENNReal.tendsto_nat_tsum (fun k => μ (A ∩ retSet T A B (k + 1)))).add (aux_induced_14 (μ := μ) (T := T) (A := A) (B := B) hT.measurable hA hB hBA)
  have hconst : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, μ (A ∩ retSet T A B (k + 1))) + μ (avoidSet T A B n)) atTop (𝓝 (μ B)) := (tendsto_const_nhds : Tendsto (fun _ : ℕ => μ B) atTop (𝓝 (μ B))).congr' (Filter.Eventually.of_forall fun n => aux_induced_12 hT hA hB n)
  have hfin := tendsto_nhds_unique hconst hsum
  simpa only [add_zero] using hfin


/-! ### 3. Poincaré recurrence and measure preservation -/

-- Mathlib: `(hT.conservative).measure_mem_forall_ge_image_notMem_eq_zero hA.nullMeasurableSet 1`
-- (`MeasurePreserving.conservative`); the two sets agree by `aux_induced_2` (`ext`, `m ≥ 1 ↔ 0 < m`).
private theorem aux_induced_16 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    μ (A ∩ {x | retTime T A x = 0}) = 0 := by
  have h : A ∩ {x | retTime T A x = 0} = {x | x ∈ A ∧ ∀ m ≥ 1, T^[m] x ∉ A} :=
    Set.ext fun x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hxA, h0⟩
        exact ⟨hxA, fun m hm => (aux_induced_2 T A x).mp h0 m (by omega)⟩
      · rintro ⟨hxA, h'⟩
        exact ⟨hxA, (aux_induced_2 T A x).mpr (fun n hn => h' n (by omega))⟩
  rw [h]
  exact hT.conservative.measure_mem_forall_ge_image_notMem_eq_zero hA.nullMeasurableSet 1


-- From `aux_induced_16`: `measure_eq_zero_iff_ae_notMem`, then `filter_upwards`; `Nat.pos_of_ne_zero`.
theorem ae_retTime_pos {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → 0 < retTime T A x := by
  have h16 := aux_induced_16 hT hA
  rw [measure_eq_zero_iff_ae_notMem] at h16
  filter_upwards [h16] with x hx hxA
  exact Nat.pos_of_ne_zero fun h0 => hx ⟨hxA, h0⟩


-- `ext x`; split on `retTime T A x = 0` (then `inducedMap x = x`, `Function.iterate_zero`) or
-- `retTime T A x = k + 1` (then `aux_induced_1` identifies `x ∈ retSet T A B (k+1)`; the converse
-- needs `T^[k+1] x ∈ B ⊆ A`, hence `hBA`).
omit [MeasurableSpace Ω] in
private theorem aux_induced_18 (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    A ∩ inducedMap T A ⁻¹' B =
      (A ∩ {x | retTime T A x = 0} ∩ B) ∪ ⋃ k : ℕ, A ∩ retSet T A B (k + 1) := by
  apply Set.ext
  intro x
  simp only [inducedMap, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union, Set.mem_iUnion,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxA, hxB⟩
    by_cases h0 : retTime T A x = 0
    · refine Or.inl ⟨⟨hxA, h0⟩, ?_⟩
      rw [h0, Function.iterate_zero] at hxB
      exact hxB
    · have hne : retTime T A x ≠ 0 := h0
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hk' : retTime T A x = k + 1 := hk
      have hchar : T^[k + 1] x ∈ A ∧ ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A :=
        (aux_induced_1 T A x (Nat.succ_pos k)).mp hk'
      rw [hk'] at hxB
      exact Or.inr ⟨k, hxA, hxB, hchar.2⟩
  · rintro (h | h)
    · obtain ⟨⟨hxA, h0⟩, hxB⟩ := h
      refine ⟨hxA, ?_⟩
      rw [h0, Function.iterate_zero]
      exact hxB
    · obtain ⟨k, hAk⟩ := h
      obtain ⟨hxA, hk⟩ := hAk
      simp only [retSet, Set.mem_setOf_eq] at hk
      have hBk : T^[k+1] x ∈ B := hk.1
      have hret : retTime T A x = k + 1 :=
        (aux_induced_1 T A x (Nat.succ_pos k)).mpr ⟨hBA hBk, hk.2⟩
      refine ⟨hxA, ?_⟩
      rw [hret]
      exact hBk


-- For `k ≠ l`, points of `A ∩ retSet … (k+1)` have `retTime = k+1` (`aux_induced_1`, using
-- `T^[k+1] x ∈ B ⊆ A`; without `hBA` this is false), so the
-- pieces are disjoint (`pairwise_disjoint_on`, `Set.disjoint_left`).
omit [MeasurableSpace Ω] in
private theorem aux_induced_19 (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => A ∩ retSet T A B (k + 1))) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact Set.disjoint_left.2 fun x hx1 hx2 => by
      simp only [Set.mem_inter_iff, retSet, Set.mem_setOf_eq] at hx1 hx2
      exact hx2.2.2 (k + 1) (Nat.succ_pos k) (Nat.succ_lt_succ h) (hBA hx1.2.1)
  · exact Set.disjoint_left.2 fun x hx1 hx2 => by
      simp only [Set.mem_inter_iff, retSet, Set.mem_setOf_eq] at hx1 hx2
      exact hx1.2.2 (l + 1) (Nat.succ_pos l) (Nat.succ_lt_succ h) (hBA hx2.2.1)


-- `aux_induced_18`; `measure_union_null`-style: the first piece is null by `aux_induced_16`
-- (`measure_mono_null`), so `μ (N ∪ U) = μ U` (`measure_union_null_iff`/`measure_union_le` and
-- `measure_mono`); `measure_iUnion aux_induced_19 (…)` and `aux_induced_15`.
private theorem aux_induced_20 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : μ (A ∩ inducedMap T A ⁻¹' B) = μ B := by
  have hUeq : μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1))
      = ∑' k : ℕ, μ (A ∩ retSet T A B (k + 1)) :=
    measure_iUnion (μ := μ) (aux_induced_19 T hBA)
      (fun k => hA.inter (aux_induced_8 hT.measurable hA hB (k + 1)).1)
  have hU : μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1)) = μ B :=
    hUeq.trans (aux_induced_15 hT hA hB hBA).symm
  have hN : μ (A ∩ {x | retTime T A x = 0} ∩ B) = 0 :=
    measure_mono_null
      (s := A ∩ {x | retTime T A x = 0} ∩ B) (t := A ∩ {x | retTime T A x = 0})
      (fun x hx => ⟨hx.1.1, hx.1.2⟩) (aux_induced_16 hT hA)
  rw [aux_induced_18 T hBA]
  apply le_antisymm
  · calc μ ((A ∩ {x | retTime T A x = 0} ∩ B) ∪ ⋃ k : ℕ, A ∩ retSet T A B (k + 1))
        ≤ μ (A ∩ {x | retTime T A x = 0} ∩ B) + μ (⋃ k : ℕ, A ∩ retSet T A B (k + 1)) :=
          measure_union_le _ _
      _ = μ B := (by rw [hN, zero_add, hU])
  · rw [← hU]
    exact measure_mono Set.subset_union_right


-- The two sets differ inside `A ∩ {retTime = 0}` (on `A ∩ {retTime ≠ 0}` the image lies in `A`,
-- `aux_induced_3`), which is null by `aux_induced_16`: `measure_congr` with an `ae_eq` from
-- `measure_eq_zero_iff_ae_notMem`, or two `measure_mono` + `measure_union_le` bounds.
omit [MeasurableSpace Ω] in
private lemma aux_induced_21a (T : Ω → Ω) (A B : Set Ω) :
    (A ∩ inducedMap T A ⁻¹' B) \ (A ∩ inducedMap T A ⁻¹' (B ∩ A)) ⊆
      A ∩ {x | retTime T A x = 0} := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨hxA, hxB⟩ := hx1
  refine ⟨hxA, ?_⟩
  by_contra hr
  exact hx2 ⟨hxA, hxB, aux_induced_3 T A x hr⟩

omit [MeasurableSpace Ω] in
private lemma aux_induced_21b (T : Ω → Ω) (A B : Set Ω) :
    (A ∩ inducedMap T A ⁻¹' (B ∩ A)) \ (A ∩ inducedMap T A ⁻¹' B) ⊆
      A ∩ {x | retTime T A x = 0} := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨hxA, hxB⟩ := hx1
  refine ⟨hxA, ?_⟩
  by_contra hr
  exact hx2 ⟨hxA, hxB.1⟩

private theorem aux_induced_21 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) :
    μ (A ∩ inducedMap T A ⁻¹' B) = μ (A ∩ inducedMap T A ⁻¹' (B ∩ A)) := by
  have hNnull : μ (A ∩ {x | retTime T A x = 0}) = 0 := aux_induced_16 hT hA
  exact measure_congr (ae_eq_set.mpr
    ⟨measure_mono_null (aux_induced_21a T A B) hNnull,
     measure_mono_null (aux_induced_21b T A B) hNnull⟩)


-- `⟨measurable_inducedMap, ?_⟩`; `Measure.ext fun B hB => ?_`; `Measure.map_apply`,
-- `Measure.restrict_apply` (twice); `Set.inter_comm`; `aux_induced_21`, then `aux_induced_20`
-- with `B ∩ A` (measurable, `⊆ A` by `inter_subset_right`).
theorem measurePreserving_inducedMap {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) := by
  refine ⟨?_, ?_⟩
  · exact measurable_inducedMap (T := T) hT.measurable hA
  · ext B hB
    have hmeas : Measurable (inducedMap T A) := measurable_inducedMap (T := T) hT.measurable hA
    rw [Measure.map_apply hmeas hB, Measure.restrict_apply (hB.preimage hmeas),
      Measure.restrict_apply hB, Set.inter_comm (inducedMap T A ⁻¹' B) A]
    rw [aux_induced_21 hT hA B,
      aux_induced_20 hT (A := A) (B := B ∩ A) hA (hB.inter hA) Set.inter_subset_right]


/-! ### 4. Ergodicity -/

-- Measurability of the first-entrance set: `⋃ n, {T^[n] x ∈ A} ∩ ⋂ j < n, {T^[j] x ∉ A} ∩
-- {T^[n] x ∈ E}` (`MeasurableSet.iUnion`, `MeasurableSet.iInter`, `aux_induced_4`).
omit [MeasurableSpace Ω] in
private theorem aux_entSet_eq {T : Ω → Ω} {A E : Set Ω} :
    entSet T A E = ⋃ n : ℕ, ({x : Ω | T^[n] x ∈ A} ∩
      (⋂ j : Fin n, {x : Ω | T^[(j : ℕ)] x ∉ A}) ∩ {x : Ω | T^[n] x ∈ E}) := by
  ext x
  simp only [entSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    exact ⟨n, ⟨h1, fun j => h2 j.val j.isLt⟩, h3⟩
  · rintro ⟨n, ⟨h1, h2⟩, h3⟩
    exact ⟨n, h1, fun j hj => h2 ⟨j, hj⟩, h3⟩

private theorem aux_induced_23 {T : Ω → Ω} (hT : Measurable T) {A E : Set Ω} (hA : MeasurableSet A)
    (hE : MeasurableSet E) : MeasurableSet (entSet T A E) := by
  rw [aux_entSet_eq]
  apply MeasurableSet.iUnion
  intro n
  exact MeasurableSet.inter
    (MeasurableSet.inter (hA.preimage (hT.iterate n))
      (MeasurableSet.iInter (fun j : Fin n => (hA.preimage (hT.iterate (j : ℕ))).compl)))
    (hE.preimage (hT.iterate n))


-- `ext x`: for `x ∈ A` the first entrance time is `0` (any `n > 0` violates `j = 0 < n`).
omit [MeasurableSpace Ω] in
private theorem aux_entSet_inter (T : Ω → Ω) (A E : Set Ω) : entSet T A E ∩ A = E ∩ A := by
  ext x
  constructor
  · intro hx
    obtain ⟨hex, hxA⟩ := hx
    rw [entSet] at hex
    obtain ⟨n, hnA, hna, hnE⟩ := hex
    have hn0 : n = 0 := by
      by_contra h
      exact hna 0 (Nat.pos_of_ne_zero h) hxA
    subst hn0
    exact ⟨by simpa using hnE, hxA⟩
  · intro hx
    obtain ⟨hxE, hxA⟩ := hx
    exact ⟨⟨0, hxA, (by intro j hj; exact absurd hj (Nat.not_lt_zero j)), hxE⟩, hxA⟩

omit [MeasurableSpace Ω] in
private theorem aux_induced_24 (T : Ω → Ω) (A E : Set Ω) : entSet T A E ∩ A = E ∩ A := by
  exact aux_entSet_inter T A E


-- `x ∉ A`: first entrance of `x` at `n+1` ↔ first entrance of `T x` at `n` (and entrance time
-- `0` is impossible).  `Function.iterate_succ_apply`; `Nat.lt_succ_iff`, case `j = 0`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_25 (T : Ω → Ω) (A E : Set Ω) {x : Ω} (hx : x ∉ A) :
    T x ∈ entSet T A E ↔ x ∈ entSet T A E := by
  simp only [entSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    refine ⟨n.succ, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply T n x]; exact h1
    · intro j hj
      cases j with
      | zero => rw [Function.iterate_zero_apply]; exact hx
      | succ m =>
          rw [Function.iterate_succ_apply T m x]
          exact h2 m (Nat.succ_lt_succ_iff.mp hj)
    · rw [Function.iterate_succ_apply T n x]; exact h3
  · rintro ⟨n, h1, h2, h3⟩
    cases n with
    | zero => rw [Function.iterate_zero_apply] at h1; exact absurd h1 hx
    | succ k =>
        refine ⟨k, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply T k x] at h1; exact h1
        · intro j hj
          rw [← Function.iterate_succ_apply T j x]
          exact h2 (j + 1) (Nat.succ_lt_succ_iff.mpr hj)
        · rw [Function.iterate_succ_apply T k x] at h3; exact h3


-- `x ∈ A`, `retTime T A x = k + 1`: `T x` first enters `A` at time `k`, at the point
-- `T^[k] (T x) = T^[k+1] x = inducedMap T A x` (`aux_induced_1`, `Function.iterate_succ_apply`),
-- so `T x ∈ entSet ↔ inducedMap T A x ∈ E`.
omit [MeasurableSpace Ω] in
private theorem aux_induced_26 (T : Ω → Ω) (A E : Set Ω) {x : Ω} {k : ℕ}
    (hk : retTime T A x = k + 1) : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := by
  have hchar := (aux_induced_1 T A x (Nat.succ_pos k)).mp hk
  have hkA : T^[k + 1] x ∈ A := hchar.1
  have hkavoid : ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A := hchar.2
  have hid : inducedMap T A x = T^[k] (T x) := by
    unfold inducedMap
    rw [hk, Function.iterate_succ_apply]
  rw [hid]
  simp only [entSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hnA, hnavoid, hnE⟩
    have hret : retTime T A x = n + 1 := by
      refine (aux_induced_1 T A x (Nat.succ_pos n)).mpr ⟨?_, ?_⟩
      · simpa only [Function.iterate_succ_apply] using hnA
      · intro j hj0 hjlt
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj0)
        simpa only [Function.iterate_succ_apply] using hnavoid m (by omega)
    have hkn : k = n := by omega
    rw [hkn]
    exact hnE
  · intro h
    refine ⟨k, ?_, ?_, h⟩
    · simpa only [Function.iterate_succ_apply] using hkA
    · intro j hj
      have h1 := hkavoid (j + 1) (Nat.succ_pos j) (by omega)
      simpa only [Function.iterate_succ_apply] using h1


-- `filter_upwards [ae_retTime_pos hT hA]`; `x ∉ A`: `aux_induced_25`; `x ∈ A`: write
-- `retTime = k+1` (`Nat.exists_eq_succ_of_ne_zero`), `aux_induced_26`, `hinv` (as `x ∈ E ↔
-- inducedMap x ∈ E`, from `Set.ext_iff`), and `aux_induced_24` (`x ∈ entSet ↔ x ∈ E` on `A`).
omit [MeasurableSpace Ω] in
private theorem aux_induced_26' (T : Ω → Ω) (A E : Set Ω) {x : Ω} {k : ℕ}
    (hk : retTime T A x = k + 1) : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := by
  have hchar : T^[k + 1] x ∈ A ∧ ∀ j, 0 < j → j < k + 1 → T^[j] x ∉ A :=
    (aux_induced_1 T A x (Nat.succ_pos k)).mp hk
  have hshift : ∀ m : ℕ, T^[m] (T x) = T^[m + 1] x :=
    fun m => (Function.iterate_succ_apply T m x).symm
  have h2' : ∀ m, m < k → T^[m] (T x) ∉ A := by
    intro m hm
    rw [hshift m]
    exact hchar.2 (m + 1) (Nat.succ_pos m) (by omega)
  constructor
  · rintro ⟨n, h1, h2, h3⟩
    have hnk : n ≤ k := by
      by_contra h
      have hlt : k < n := by omega
      have hkA : T^[k] (T x) ∉ A := h2 k hlt
      rw [hshift k] at hkA
      exact hkA hchar.1
    have hkn : k ≤ n := by
      by_contra h
      have hlt : n < k := by omega
      exact h2' n hlt h1
    have hnk' : n = k := le_antisymm hnk hkn
    have hid : inducedMap T A x = T^[n] (T x) := by
      rw [inducedMap, hk, ← hshift k, ← hnk']
    rwa [hid]
  · intro hE
    have hkE : T^[k] (T x) ∈ E := by
      rw [hshift k]
      rw [inducedMap, hk] at hE
      exact hE
    exact ⟨k, by rw [hshift k]; exact hchar.1, fun j hj => h2' j hj, hkE⟩

omit [MeasurableSpace Ω] in
private theorem aux_induced_29 (T : Ω → Ω) (A E : Set Ω) (hinv : inducedMap T A ⁻¹' E = E)
    {x : Ω} (hxA : x ∈ A) {k : ℕ} (hk : retTime T A x = k + 1) :
    T x ∈ entSet T A E ↔ x ∈ entSet T A E := by
  have h26 : T x ∈ entSet T A E ↔ inducedMap T A x ∈ E := aux_induced_26' T A E hk
  have h6 : inducedMap T A x ∈ E ↔ x ∈ E := by simpa using Set.ext_iff.mp hinv x
  have hh := Set.ext_iff.mp (aux_entSet_inter T A E) x
  rw [Set.mem_inter_iff, Set.mem_inter_iff] at hh
  have hiff : x ∈ entSet T A E ↔ x ∈ E :=
    ⟨fun h1 => (hh.mp ⟨h1, hxA⟩).1, fun h1 => (hh.mpr ⟨h1, hxA⟩).1⟩
  exact h26.trans (h6.trans hiff.symm)

omit [MeasurableSpace Ω] in
private theorem aux_induced_28a (T : Ω → Ω) (A E : Set Ω) (hinv : inducedMap T A ⁻¹' E = E) :
    T ⁻¹' entSet T A E \ entSet T A E ⊆ A ∩ {x | retTime T A x = 0} := by
  intro x hx
  simp only [Set.mem_sdiff] at hx
  obtain ⟨hxT, hxnot⟩ := hx
  rw [Set.mem_preimage] at hxT
  have hxA : x ∈ A := by
    by_contra h
    exact hxnot ((aux_induced_25 T A E h).mp hxT)
  refine ⟨hxA, ?_⟩
  by_contra h0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact hxnot ((aux_induced_29 T A E hinv hxA hk).mp hxT)

omit [MeasurableSpace Ω] in
private theorem aux_induced_28b (T : Ω → Ω) (A E : Set Ω) (hinv : inducedMap T A ⁻¹' E = E) :
    entSet T A E \ T ⁻¹' entSet T A E ⊆ A ∩ {x | retTime T A x = 0} := by
  intro x hx
  simp only [Set.mem_sdiff] at hx
  obtain ⟨hxent, hxT⟩ := hx
  rw [Set.mem_preimage] at hxT
  have hxA : x ∈ A := by
    by_contra h
    exact hxT ((aux_induced_25 T A E h).mpr hxent)
  refine ⟨hxA, ?_⟩
  by_contra h0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact hxT ((aux_induced_29 T A E hinv hxA hk).mpr hxent)

private theorem aux_induced_27 {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A E : Set Ω} (hA : MeasurableSet A)
    (hinv : inducedMap T A ⁻¹' E = E) :
    T ⁻¹' entSet T A E =ᵐ[μ] entSet T A E := by
  rw [MeasureTheory.ae_eq_set]
  exact ⟨measure_mono_null (aux_induced_28a T A E hinv) (aux_induced_16 hT hA),
    measure_mono_null (aux_induced_28b T A E hinv) (aux_induced_16 hT hA)⟩


-- Transfer: `eventuallyConst_set'` on both sides.  If `S =ᵐ[μ] ∅` (resp. `univ`) then
-- `E =ᵐ[μ.restrict A] ∅` (resp. `univ`) because `E ∩ A = S ∩ A`: use `ae_restrict_iff'`/
-- `ae_restrict_of_ae` and `Set.ext_iff` on `hES`.
private theorem aux_induced_28 {μ : Measure Ω} {A E S : Set Ω} (hA : MeasurableSet A)
    (hES : S ∩ A = E ∩ A) (hS : EventuallyConst S (ae μ)) :
    EventuallyConst E (ae (μ.restrict A)) := by
  rw [Filter.eventuallyConst_set] at hS ⊢
  rcases hS with hS | hS
  · left
    rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards [hS] with x hx hxA
    exact ((Set.ext_iff.mp hES x).mp ⟨hx, hxA⟩).1
  · right
    rw [MeasureTheory.ae_restrict_iff' hA]
    filter_upwards [hS] with x hx hxA
    exact fun hE => hx ((Set.ext_iff.mp hES x).mpr ⟨hE, hxA⟩).1


-- `⟨measurePreserving_inducedMap herg.toMeasurePreserving hA, ⟨fun E hE hinv => ?_⟩⟩`;
-- `herg.quasiErgodic.aeconst_set₀ (aux_induced_23 …).nullMeasurableSet (aux_induced_27 …)`
-- (Mathlib `QuasiErgodic.aeconst_set₀`, `Ergodic.quasiErgodic`), then `aux_induced_28` with
-- `aux_induced_24`.
private theorem aux_induced_29b {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω} (herg : Ergodic T μ)
    {A : Set Ω} (hA : MeasurableSet A) :
    Ergodic (inducedMap T A) (μ.restrict A) := by
  refine ⟨measurePreserving_inducedMap herg.toMeasurePreserving hA, ?_⟩
  refine ⟨fun E hE hinv => ?_⟩
  exact aux_induced_28 hA (aux_induced_24 T A E)
    (herg.quasiErgodic.aeconst_set₀
      (aux_induced_23 herg.toMeasurePreserving.measurable hA hE).nullMeasurableSet
      (aux_induced_27 herg.toMeasurePreserving hA hinv))


/-! ### 5. Iterates of the induced map (used by `kingman-linear`) -/

-- Induction on `j`: `birkhoffSum_zero`, and
-- `birkhoffSum S r (j+1) x = birkhoffSum S r j x + r (S^[j] x)` (Mathlib `birkhoffSum_succ`),
-- `Function.iterate_succ_apply'`, `Function.iterate_add_apply`.
omit [MeasurableSpace Ω] in
theorem inducedMap_iterate (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (inducedMap T A)^[j] x = T^[birkhoffSum (inducedMap T A) (retTime T A) j x] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, birkhoffSum_succ, ih, inducedMap,
      ← Function.iterate_add_apply, Nat.add_comm]


-- `(measurePreserving_inducedMap hT hA).iterate i` gives quasi-measure-preservation of `S^[i]` for
-- `μ.restrict A`; pull back `ae_retTime_pos` restricted to `A` (`ae_restrict_iff'`) along it
-- (`QuasiMeasurePreserving.ae`), then `ae_all_iff`.
theorem inducedMap_ae_retTime_pos {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∀ i : ℕ, 0 < retTime T A ((inducedMap T A)^[i] x) := by
  have h1 : ∀ᵐ x ∂(μ.restrict A), 0 < retTime T A x :=
    (ae_restrict_iff' hA).2 (ae_retTime_pos hT hA)
  have hS : MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) :=
    measurePreserving_inducedMap hT hA
  rw [ae_all_iff]
  intro i
  exact ((hS.iterate i).quasiMeasurePreserving).ae h1


/-! ### Main theorem -/

/-- **The induced map.**  Poincaré recurrence on `A`, invariance of `μ.restrict A` under the
first-return map, and ergodicity of the first-return map when `T` is ergodic. -/
theorem induced_map (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    (∀ᵐ x ∂μ, x ∈ A → 0 < retTime T A x) ∧
    MeasurePreserving (inducedMap T A) (μ.restrict A) (μ.restrict A) ∧
    (Ergodic T μ → Ergodic (inducedMap T A) (μ.restrict A)) :=
  ⟨ae_retTime_pos hT hA, measurePreserving_inducedMap hT hA, fun herg => aux_induced_29b herg hA⟩

end LatticeProb
