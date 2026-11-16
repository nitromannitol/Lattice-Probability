import LatticeProb.ReflectedGMS.GMS.VariableRadiusCodedAdmissible
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Measurability of indexed conductance discrepancies -/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace ReflectedGMS.GMS.ValidCodeSet

open Code

noncomputable local instance : MeasurableSpace Cell := borel _
local instance : BorelSpace Cell := ⟨rfl⟩

/-- The indexed conductance discrepancy with active slots and exact image matches. -/
noncomputable def indexedConductanceDiscrepancy
    (r : ℝ) (x y : RawCode) (F : C(Plane, Plane)) : ENNReal := by
  classical
  exact
  ⨆ (i : ℕ) (i' : ℕ) (j : ℕ) (j' : ℕ),
    if SlotNear 0 r (x.1 i) ∧ SlotNear 0 r (x.1 i') ∧
      SlotNear 0 r (y.1 j) ∧ SlotNear 0 r (y.1 j') ∧
      (slotCell x i).map F F.continuous = slotCell y j ∧
      (slotCell x i').map F F.continuous = slotCell y j' ∧ 0 < x.2 i i'
    then ENNReal.ofReal |x.2 i i' - y.2 j j'| else 0

/-- The indexed conductance discrepancy is jointly measurable in the radius, codes and map. -/
theorem measurable_indexedConductanceDiscrepancy
    {Ω : Type*} [MeasurableSpace Ω] (r : Ω → ℝ) (x y : Ω → RawCode)
    (F : Ω → C(Plane, Plane)) (hr : Measurable r) (hx : Measurable x)
    (hy : Measurable y) (hF : Measurable F) :
    Measurable fun ω => indexedConductanceDiscrepancy (r ω) (x ω) (y ω) (F ω) := by
  classical
  have hmatch (i j : ℕ) : MeasurableSet {ω |
      (slotCell (x ω) i).map (F ω) (F ω).continuous = slotCell (y ω) j} := by
    let S : Set (C(Plane, Plane) × Cell × Cell) :=
      {p | p.2.1.map p.1 p.1.continuous = p.2.2}
    have hS : IsClosed S := by
      exact LatticeProb.isClosed_nonemptyCompacts_image_eq Prod.fst
        (fun p : C(Plane, Plane) × Cell × Cell => p.2.1) (fun p => p.2.2)
        continuous_fst (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)
    exact hS.measurableSet.preimage
      (hF.prodMk (((measurable_slotCell i).comp hx).prodMk ((measurable_slotCell j).comp hy)))
  unfold indexedConductanceDiscrepancy
  refine Measurable.iSup fun i => Measurable.iSup fun i' =>
    Measurable.iSup fun j => Measurable.iSup fun j' => ?_
  apply Measurable.ite
  · exact (measurableSet_slotNear_variable_radius x r hx hr 0 i).inter <|
      (measurableSet_slotNear_variable_radius x r hx hr 0 i').inter <|
      (measurableSet_slotNear_variable_radius y r hy hr 0 j).inter <|
      (measurableSet_slotNear_variable_radius y r hy hr 0 j').inter <|
      (hmatch i j).inter <| (hmatch i' j').inter <|
      measurableSet_lt measurable_const ((measurable_rawCond i i').comp hx)
  · simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply] using ENNReal.measurable_ofReal.comp
      ((((measurable_rawCond i i').comp hx).sub ((measurable_rawCond j j').comp hy)).norm)
  · exact measurable_const

end ReflectedGMS.GMS.ValidCodeSet
