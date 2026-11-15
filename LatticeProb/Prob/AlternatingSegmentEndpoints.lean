import LatticeProb.Prob.AlternatingExcursionCount
import LatticeProb.Prob.OpenEntryClockEndpoints

/-! # Endpoints of alternating excursion segments -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- Every clock before the totalized first infinite-clock index is finite. -/
theorem firstInfiniteClockIndex_ne_top_of_lt {Ω : Type*}
    (e : ℕ → Ω → WithTop ℝ) (ω : Ω) (n : ℕ)
    (hn : n < firstInfiniteClockIndex e ω) : e n ω ≠ ⊤ := by
  classical
  by_cases h : ∃ j, e j ω = ⊤
  · exact (firstInfiniteClockIndex_spec e ω h).2 n hn
  · have hz : firstInfiniteClockIndex e ω = 0 :=
      firstInfiniteClockIndex_eq_zero_of_forall_ne_top e ω (by simpa only [not_exists] using h)
    simp only [hz, Nat.not_lt_zero] at hn

/-- Before the excursion count, both endpoints are finite and ordered. -/
theorem alternatingSegmentEndpoints_of_lt {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    (U V : Set (EuclideanSpace ℝ (Fin d))) (ω : Ω) (n : ℕ)
    (hn : n < alternatingExcursionCount f a U V ω) :
    let x := alternatingExitClock f a U V n ω
    let y := openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω
    x ≠ ⊤ ∧ y ≠ ⊤ ∧ x ≤ y := by
  dsimp only
  have hy : openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω ≠ ⊤ :=
    firstInfiniteClockIndex_ne_top_of_lt _ ω n hn
  have hle := le_openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω
  exact ⟨fun hx => hy (top_le_iff.mp (hx ▸ hle)), hy, hle⟩

/-- The totalized real exit and entry endpoints at a fixed index are measurable. -/
theorem measurable_alternatingSegmentEndpoints {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) (ha : Measurable a) (n : ℕ) :
    Measurable (fun ω => ((alternatingExitClock f a U V n ω).untopD 0,
      (openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω).untopD 0)) :=
  ((measurable_alternatingExitClock f a hU hV hf ha n).untopD 0).prodMk
    ((measurable_alternatingEntryClock f a hU hV hf ha n).untopD 0)

/-- A measurable natural index can select from a countable family of measurable maps. -/
theorem measurable_nat_select {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (g : ℕ → Ω → E) (hg : ∀ n, Measurable (g n))
    (N : Ω → ℕ) (hN : Measurable N) : Measurable (fun ω => g (N ω) ω) := by
  intro s hs
  change MeasurableSet {ω | g (N ω) ω ∈ s}
  have heq : {ω | g (N ω) ω ∈ s} = ⋃ n, ({ω | N ω = n} ∩ {ω | g n ω ∈ s}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨N ω, rfl, h⟩
    · rintro ⟨n, rfl, h⟩
      exact h
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_eq_fun hN measurable_const).inter (hg n hs)

/-- The totalized real endpoints selected by a measurable index are measurable. -/
theorem measurable_selectedAlternatingSegmentEndpoints
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) (ha : Measurable a) (N : Ω → ℕ) (hN : Measurable N) :
    Measurable (fun ω => ((alternatingExitClock f a U V (N ω) ω).untopD 0,
      (openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V (N ω)) U ω).untopD 0)) :=
  measurable_nat_select _ (measurable_alternatingSegmentEndpoints f a hU hV hf ha) N hN

end LatticeProb
