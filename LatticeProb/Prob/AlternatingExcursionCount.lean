import LatticeProb.Prob.TransientAlternatingTermination
import LatticeProb.Prob.GlobalEntryClock

/-! # Measurable counts of alternating excursions -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace LatticeProb

private theorem clockIndexExists {Ω : Type*} (e : ℕ → Ω → WithTop ℝ)
    (ω : Ω) : ∃ n, e n ω = ⊤ ∨ (n = 0 ∧ ¬ ∃ j, e j ω = ⊤) := by
  classical
  by_cases h : ∃ j, e j ω = ⊤
  · obtain ⟨j, hj⟩ := h
    exact ⟨j, Or.inl hj⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

/-- The first index with an infinite entry clock, defaulting to zero if there is none. -/
noncomputable def firstInfiniteClockIndex {Ω : Type*} (e : ℕ → Ω → WithTop ℝ)
    (ω : Ω) : ℕ := by
  classical
  exact Nat.find (clockIndexExists e ω)

/-- The first infinite-clock index is measurable. -/
theorem measurable_firstInfiniteClockIndex {Ω : Type*} [MeasurableSpace Ω]
    (e : ℕ → Ω → WithTop ℝ) (he : ∀ n, Measurable (e n)) :
    Measurable (firstInfiniteClockIndex e) := by
  classical
  let p : Ω → ℕ → Prop := fun ω n =>
    e n ω = ⊤ ∨ (n = 0 ∧ ¬ ∃ j, e j ω = ⊤)
  have hp : ∀ ω, ∃ n, p ω n := by
    intro ω
    by_cases h : ∃ j, e j ω = ⊤
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
  have hm : ∀ n, MeasurableSet {ω | p ω n} := by
    intro n
    have hn : MeasurableSet {ω | e n ω = ⊤} :=
      measurableSet_eq_fun (he n) measurable_const
    have hex : MeasurableSet {ω | ∃ j, e j ω = ⊤} := by
      simpa only [ofPred_exists] using
        MeasurableSet.iUnion (fun j => measurableSet_eq_fun (he j) measurable_const)
    exact hn.union ((MeasurableSet.const (n = 0)).inter hex.compl)
  exact measurable_find hp hm

/-- When an infinite clock exists, the chosen clock is infinite and all earlier clocks are finite. -/
theorem firstInfiniteClockIndex_spec {Ω : Type*} (e : ℕ → Ω → WithTop ℝ)
    (ω : Ω) (h : ∃ n, e n ω = ⊤) :
    e (firstInfiniteClockIndex e ω) ω = ⊤ ∧
      ∀ n < firstInfiniteClockIndex e ω, e n ω ≠ ⊤ := by
  classical
  unfold firstInfiniteClockIndex
  constructor
  · rcases Nat.find_spec (clockIndexExists e ω) with ht | ⟨_, hn⟩
    · exact ht
    · exact (hn h).elim
  · intro n hn ht
    exact (Nat.find_min (clockIndexExists e ω) hn) (Or.inl ht)

/-- If no infinite clock exists, the index is totalized by zero. -/
theorem firstInfiniteClockIndex_eq_zero_of_forall_ne_top {Ω : Type*}
    (e : ℕ → Ω → WithTop ℝ) (ω : Ω) (h : ∀ n, e n ω ≠ ⊤) :
    firstInfiniteClockIndex e ω = 0 := by
  classical
  unfold firstInfiniteClockIndex
  apply (Nat.find_eq_zero (clockIndexExists e ω)).mpr
  exact Or.inr ⟨rfl, by simpa only [not_exists] using h⟩

/-- The first infinite inner-entry index, or zero if no entry is infinite. -/
noncomputable def alternatingExcursionCount {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    (U V : Set (EuclideanSpace ℝ (Fin d))) (ω : Ω) : ℕ :=
  firstInfiniteClockIndex
    (fun n => openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U) ω

/-- The alternating excursion count is measurable for measurable paths and initial clock. -/
theorem measurable_alternatingExcursionCount {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) (ha : Measurable a) :
    Measurable (alternatingExcursionCount f a U V) :=
  measurable_firstInfiniteClockIndex _ (measurable_alternatingEntryClock f a hU hV hf ha)

/-- Transience makes the selected entry infinite, with all previous entries finite. -/
theorem alternatingExcursionCount_spec_of_transient
    {Ω : Type*} {d : ℕ} (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)))
    (a : Ω → WithTop ℝ) (ω : Ω) (U V : Set (EuclideanSpace ℝ (Fin d)))
    (htr : Tendsto (f ω) (cocompact ℝ) (cocompact _))
    (hU : Bornology.IsBounded U) (hV : IsOpen V) (hUV : closure U ⊆ V) :
    let e := fun n => openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω
    e (alternatingExcursionCount f a U V ω) = ⊤ ∧
      ∀ n < alternatingExcursionCount f a U V ω, e n ≠ ⊤ :=
  firstInfiniteClockIndex_spec _ ω
    (exists_top_alternatingEntryClock_of_transient f a ω U V htr hU hV hUV)

/-- The count initialized by the global entry clock into the outer open set is measurable. -/
theorem measurable_globalEntry_alternatingExcursionCount
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d)))
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) :
    Measurable (alternatingExcursionCount f
      (fun ω => entryClockOfEReal (globalOpenEntry (fun ω t => f ω t) V ω)) U V) := by
  apply measurable_alternatingExcursionCount f _ hU hV hf
  exact measurable_globalEntryClock _ hV (fun ω => (f ω).continuous)
    (fun q => (continuous_eval_const (q : ℝ)).measurable.comp hf)

end LatticeProb
