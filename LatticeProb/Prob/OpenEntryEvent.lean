import Mathlib

/-! # Open-set entry events for continuous paths -/

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace LatticeProb

/-- For continuous paths, an entry into an open set before a fixed time and at
or after a measurable starting time is a measurable event. -/
theorem measurableSet_exists_open_entry {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → ℝ → E) (a : Ω → ℝ) (b : ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ q : ℚ, Measurable fun ω => f ω q)
    (ha : Measurable a) :
    MeasurableSet {ω | ∃ t, a ω ≤ t ∧ t < b ∧ f ω t ∈ U} := by
  have heq : {ω | ∃ t, a ω ≤ t ∧ t < b ∧ f ω t ∈ U} =
      ⋃ q : ℚ, {ω | a ω < (q : ℝ) ∧ (q : ℝ) < b ∧ f ω q ∈ U} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, hat, htb, htU⟩
      have htopen : IsOpen ((f ω) ⁻¹' U) := hU.preimage (hf ω)
      obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (htopen.mem_nhds htU)
      obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_min htb hr)
      exact ⟨q, hat.trans_lt htq, (lt_min_iff.mp hq).1,
        hsub ⟨hl.trans htq, (lt_min_iff.mp hq).2⟩⟩
    · rintro ⟨q, ha, hb, hq⟩
      exact ⟨q, ha.le, hb, hq⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  by_cases hqb : (q : ℝ) < b
  · simp only [hqb, true_and]
    change MeasurableSet ({ω | a ω < (q : ℝ)} ∩ (fun ω => f ω q) ⁻¹' U)
    exact (measurableSet_lt ha measurable_const).inter (hU.measurableSet.preimage (hm q))
  · simpa only [hqb, false_and, and_false, ofPred_false] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))

end LatticeProb
