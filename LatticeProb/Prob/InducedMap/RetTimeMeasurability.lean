import Mathlib
import LatticeProb.Prob.ReturnTime

/-!
# Measurability of the return time and the first-return map

`retTime T A x` (from `LatticeProb.Prob.ReturnTime`) is the first `n > 0` with `T^[n] x ∈ A`
(and `0` if there is none), and `inducedMap T A x = T^[retTime T A x] x` is the first-return
map. This file characterises `retTime T A x = n`, shows each level set of `retTime` is
measurable, and concludes that `retTime T A` and `inducedMap T A` are measurable when `T` is.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- For `0 < n`, `retTime T A x = n` iff `T^[n] x ∈ A` and no positive time below `n` lands
in `A`. -/
theorem retTime_eq_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) {n : ℕ} (hn : 0 < n) :
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

omit [MeasurableSpace Ω] in
/-- `retTime T A x = 0` iff `x` never returns to `A` at a positive time. -/
theorem retTime_eq_zero_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) :
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

omit [MeasurableSpace Ω] in
/-- If `x` returns to `A`, its first-return point `inducedMap T A x` lies in `A`. -/
theorem inducedMap_mem_of_retTime_ne_zero (T : Ω → Ω) (A : Set Ω) (x : Ω)
    (hx : retTime T A x ≠ 0) : inducedMap T A x ∈ A := by
  have hpos : 0 < retTime T A x := Nat.pos_of_ne_zero hx
  have h := (retTime_eq_iff T A x hpos).mp rfl
  simpa [inducedMap] using h.1

/-- `{x | T^[n] x ∈ A}` is measurable, as the preimage of `A` under the measurable map `T^[n]`. -/
theorem measurableSet_setOf_iterate_mem {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (n : ℕ) : MeasurableSet {x | T^[n] x ∈ A} := by
  exact hA.preimage (hT.iterate n)

/-- The set of points that never visit `A` at a positive time is measurable. -/
private theorem measurableSet_setOf_forall_iterate_notMem (T : Ω → Ω) (hT : Measurable T)
    (A : Set Ω) (hA : MeasurableSet A) :
    MeasurableSet {x : Ω | ∀ m, 0 < m → T^[m] x ∉ A} := by
  rw [Set.setOf_forall]
  refine MeasurableSet.iInter (fun m => ?_)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [show {x : Ω | 0 < m → T^[m] x ∉ A} = {x : Ω | T^[m] x ∉ A} from
      Set.ext (fun x => by simp [hm])]
    exact (hA.preimage (hT.iterate m)).compl

/-- The set of points avoiding `A` at every positive time below `n` is measurable. -/
private theorem measurableSet_setOf_forall_lt_iterate_notMem (T : Ω → Ω) (hT : Measurable T)
    (A : Set Ω) (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {x : Ω | ∀ j, 0 < j → j < n → T^[j] x ∉ A} := by
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

/-- Each level set `{x | retTime T A x = n}` of the return time is measurable. -/
private theorem measurableSet_setOf_retTime_eq {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) (n : ℕ) : MeasurableSet {x | retTime T A x = n} := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hset : {x : Ω | retTime T A x = 0} = {x : Ω | ∀ m, 0 < m → T^[m] x ∉ A} := by
      ext x; exact retTime_eq_zero_iff T A x
    rw [hset]
    exact measurableSet_setOf_forall_iterate_notMem T hT A hA
  · have hset : {x : Ω | retTime T A x = n} =
        {x : Ω | T^[n] x ∈ A} ∩ {x : Ω | ∀ j, 0 < j → j < n → T^[j] x ∉ A} := by
      ext x; exact retTime_eq_iff T A x hn
    rw [hset]
    exact (measurableSet_setOf_iterate_mem hT hA n).inter
      (measurableSet_setOf_forall_lt_iterate_notMem T hT A hA n)

/-- The return time `retTime T A` is measurable, by countable-valued measurability from the
measurability of each level set. -/
theorem measurable_retTime {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (retTime T A) := by
  exact measurable_to_countable' fun n => measurableSet_setOf_retTime_eq hT hA n

/-- The first-return map `inducedMap T A` is measurable, as the composition of the jointly
measurable iterate map `(x, n) ↦ T^[n] x` with `x ↦ (x, retTime T A x)`. -/
theorem measurable_inducedMap {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable (inducedMap T A) := by
  have h1 : Measurable (fun p : Ω × ℕ => T^[p.2] p.1) :=
    measurable_from_prod_countable_left (fun n => hT.iterate n)
  have h2 : Measurable (fun x : Ω => (x, retTime T A x)) :=
    measurable_id.prodMk (measurable_retTime hT hA)
  exact h1.comp h2

end LatticeProb
