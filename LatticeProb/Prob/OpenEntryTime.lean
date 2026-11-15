import LatticeProb.Prob.OpenEntryEvent

/-! # Measurability of open-set hitting times -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace LatticeProb

/-- The first entry into an open set after a measurable real time is measurable,
with `⊤` used when there is no entry. -/
theorem measurable_open_hittingAfter {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → ℝ → E) (a : Ω → ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ q : ℚ, Measurable fun ω => f ω q)
    (ha : Measurable a) :
    Measurable fun ω => hittingAfter (fun t ω => f ω t) U (a ω) ω := by
  let T : Ω → WithTop ℝ := fun ω => hittingAfter (fun t ω => f ω t) U (a ω) ω
  have hfinite (b : ℝ) : MeasurableSet {ω | T ω < (b : WithTop ℝ)} := by
    have heq : {ω | T ω < (b : WithTop ℝ)} =
        {ω | ∃ t, a ω ≤ t ∧ t < b ∧ f ω t ∈ U} := by
      ext ω
      simpa only [T, mem_ofPred_eq, mem_Ico, and_assoc] using
        (hittingAfter_lt_iff (u := fun t ω => f ω t) (s := U)
          (n := a ω) (ω := ω) (i := b))
    rw [heq]
    exact measurableSet_exists_open_entry f a b hU hf hm ha
  apply measurable_of_Iio
  intro b
  change MeasurableSet {ω | T ω < b}
  induction b using WithTop.recTopCoe with
  | top =>
      have heq : {ω | T ω < ⊤} = ⋃ n : ℕ, {ω | T ω < ((n : ℝ) : WithTop ℝ)} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iUnion]
        constructor
        · intro h
          have hne : T ω ≠ ⊤ := ne_of_lt h
          obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
          obtain ⟨n, hn⟩ := exists_nat_gt t
          exact ⟨n, by rw [← ht]; exact_mod_cast hn⟩
        · rintro ⟨n, hn⟩
          exact hn.trans_le le_top
      rw [heq]
      exact MeasurableSet.iUnion fun n => hfinite n
  | coe b => exact hfinite b

end LatticeProb
