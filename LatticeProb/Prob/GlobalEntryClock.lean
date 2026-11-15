import LatticeProb.Prob.GlobalOpenEntry

/-! # Conversion of global entry times -/

set_option autoImplicit false

open Set MeasureTheory Classical

namespace LatticeProb

/-- Convert an extended real to a clock with a single infinite endpoint.
The negative infinite endpoint is assigned zero. -/
noncomputable def entryClockOfEReal (x : EReal) : WithTop ℝ :=
  if x = ⊤ then ⊤ else (x.toReal : WithTop ℝ)

@[simp] theorem entryClockOfEReal_top : entryClockOfEReal ⊤ = ⊤ := by
  simp [entryClockOfEReal]

@[simp] theorem entryClockOfEReal_coe (t : ℝ) :
    entryClockOfEReal (t : EReal) = (t : WithTop ℝ) := by
  simp [entryClockOfEReal]

/-- On the complement of negative infinity the conversion recovers the input. -/
theorem entryClockOfEReal_spec {x : EReal} (hx : x ≠ ⊥) :
    x = ⊤ ∧ entryClockOfEReal x = ⊤ ∨
      ∃ t : ℝ, x = (t : EReal) ∧ entryClockOfEReal x = (t : WithTop ℝ) := by
  by_cases h : x = ⊤
  · exact Or.inl ⟨h, h ▸ entryClockOfEReal_top⟩
  · refine Or.inr ⟨x.toReal, (EReal.coe_toReal h hx).symm, ?_⟩
    simp [entryClockOfEReal, h]

/-- The conversion is Borel measurable, including at both infinite endpoints. -/
theorem measurable_entryClockOfEReal : Measurable entryClockOfEReal := by
  unfold entryClockOfEReal
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
    measurable_const (WithTop.measurable_coe.comp measurable_ereal_toReal)

/-- A lower bound on hit times rules out negative infinity as the global entry. -/
theorem globalOpenEntry_ne_bot_of_lower_bound {Ω E : Type*} (f : Ω → ℝ → E)
    (U : Set E) (ω : Ω) (a : ℝ) (ha : ∀ t, f ω t ∈ U → a ≤ t) :
    globalOpenEntry f U ω ≠ ⊥ := by
  have h : (a : EReal) ≤ globalOpenEntry f U ω := by
    apply le_sInf
    rintro x ⟨t, ht, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (ha t ht)
  exact ne_bot_of_gt ((EReal.coe_ne_bot a).bot_lt.trans_le h)

/-- The global open entry converted to a one-sided extended-real clock is measurable. -/
theorem measurable_globalEntryClock {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → ℝ → E) {U : Set E} (hU : IsOpen U)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ q : ℚ, Measurable fun ω => f ω q) :
    Measurable (fun ω => entryClockOfEReal (globalOpenEntry f U ω)) :=
  measurable_entryClockOfEReal.comp (measurable_globalOpenEntry f hU hf hm)

end LatticeProb
