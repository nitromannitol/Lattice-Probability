import LatticeProb.Bonanno.LQGMetric.Meas.LocalEvent
import Mathlib.MeasureTheory.Measure.Count

/-! # Measurable descent of binary codes -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A measurable binary code which is constant on the fibres of a measurable observation
on a measurable set has a measurable decoder agreeing with it everywhere on that set. -/
theorem exists_measurable_binary_decoder_of_fibre_constancy
    {Ω X ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {W : Ω → X} (hW : Measurable W)
    {Y : Ω → ι → Bool} (hY : Measurable Y) {G : Set Ω} (hG : MeasurableSet G)
    (hconst : ∀ x ∈ G, ∀ y ∈ G, W x = W y → Y x = Y y) :
    ∃ d : X → ι → Bool, Measurable d ∧ ∀ x ∈ G, Y x = d (W x) := by
  classical
  have hsep (i : ι) : ∃ S : Set X, MeasurableSet S ∧
      ∀ x ∈ G, (Y x i = true ↔ W x ∈ S) := by
    let B : Set Ω := {x | Y x i = true}
    have hB : MeasurableSet B :=
      measurableSet_eq_fun ((measurable_pi_apply i).comp hY) measurable_const
    obtain ⟨S, hS, hEq⟩ := LQGMetric.LocalEvent.ae_preimage_eq_of_saturated
      (P := Measure.count.restrict G) (Y := id) (R := W) hW hG (hG.inter hB)
      (ae_restrict_mem hG) (by
        intro x hx y hy hxy hxb
        change Y y i = true
        rw [← hconst x hx y hy hxy]
        exact hxb)
    refine ⟨S, hS, ?_⟩
    have hpoint := Measure.ae_count_iff.mp ((ae_restrict_iff' hG).mp hEq)
    intro x hx
    exact iff_of_eq (hpoint x hx)
  choose S hS hpoint using hsep
  let d : X → ι → Bool := fun x i => if x ∈ S i then true else false
  refine ⟨d, ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro i
    exact Measurable.ite (hS i) measurable_const measurable_const
  · intro x hx
    funext i
    have h := hpoint i x hx
    cases hy : Y x i <;> simp [d, hy] at h ⊢
    · exact h
    · exact h

end LatticeProb
