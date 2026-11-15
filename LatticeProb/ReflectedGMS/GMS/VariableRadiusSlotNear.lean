import LatticeProb.Bonanno.ReflectedGMS.GMS.ValidCodeSet
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Joint measurability of slot nearness and radius -/

set_option autoImplicit false

open Set TopologicalSpace

namespace ReflectedGMS.GMS.ValidCodeSet

open Code

noncomputable local instance : MeasurableSpace Cell := borel _
local instance : BorelSpace Cell := ⟨rfl⟩

/-- Slot nearness is measurable jointly in a raw code and a real radius. -/
theorem measurableSet_slotNear_variable_radius
    {Ω : Type*} [MeasurableSpace Ω] (x : Ω → RawCode) (r : Ω → ℝ)
    (hx : Measurable x) (hr : Measurable r) (q : Plane) (n : ℕ) :
    MeasurableSet {ω | SlotNear q (r ω) ((x ω).1 n)} := by
  have hdist : Measurable (fun ω => Metric.infDist q (slotCell (x ω) n : Set Plane)) :=
    (NonemptyCompacts.lipschitz_infDist_const q).continuous.measurable.comp
      ((measurable_slotCell n).comp hx)
  have hocc : MeasurableSet {ω | ((x ω).1 n).isSome = true} :=
    measurableSet_setOfPred.2 ((measurable_isSome n).comp hx)
  have heq : {ω | SlotNear q (r ω) ((x ω).1 n)} =
      {ω | ((x ω).1 n).isSome = true} ∩
        {ω | Metric.infDist q (slotCell (x ω) n : Set Plane) < r ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    cases hs : (x ω).1 n with
    | none => simp [SlotNear]
    | some K => simp [SlotNear, slotCell_of_eq_some hs]
  rw [heq]
  exact hocc.inter (measurableSet_lt hdist hr)

end ReflectedGMS.GMS.ValidCodeSet
