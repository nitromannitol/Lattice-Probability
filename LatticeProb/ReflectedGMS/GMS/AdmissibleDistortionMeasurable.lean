import LatticeProb.ReflectedGMS.GMS.AdmissibleConductanceMeasurable

/-! # Measurability of admissibility-gated distortions -/

set_option autoImplicit false

open Set Topology
open scoped Classical

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- The global displacement of a measurable family of continuous plane maps is measurable. -/
theorem measurable_global_displacement
    {Ω : Type*} [MeasurableSpace Ω] (F : Ω → C(Plane, Plane))
    (hF : Measurable F) : Measurable fun ω => ⨆ z : Plane, edist z (F ω z) := by
  have hm : Measurable (⨆ z : Plane, fun ω => edist z (F ω z)) :=
    measurable_iSup_of_lowerSemicontinuous
      (fun z => measurable_const.edist ((ContinuousMap.measurable_eval z).comp hF))
      (fun ω => (continuous_id.edist (F ω).continuous).lowerSemicontinuous)
  have heq : (fun ω => ⨆ z : Plane, edist z (F ω z)) =
      (⨆ z : Plane, fun ω => edist z (F ω z)) := by
    funext ω
    exact (iSup_apply (f := fun z : Plane => fun ω => edist z (F ω z)) (a := ω)).symm
  rw [heq]
  exact hm

/-- The decoded distortion, set to zero outside the admissible event, is measurable. -/
theorem measurable_admissible_decoded_distortion
    {Ω : Type*} [MeasurableSpace Ω] (r : Ω → ℝ) (x y : Ω → RawCode)
    (f : Ω → Plane ≃ₜ Plane)
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y)
    (hf : Measurable fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)))
    (hfi : Measurable fun ω =>
      (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane)))
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω)) :
    Measurable fun ω =>
      if AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω) then
        distortion (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω)
      else 0 := by
  classical
  have hA := measurableSet_admissibleAt_decodeConfig_variable_radius
    r x y f hx hy hr hgx hgy hf hfi
  have hd := measurable_global_displacement
    (fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane))) hf
  have hc := measurable_admissible_decoded_conductance_iSup r x y f
    hr hx hy hf hfi hgx hgy
  have hdgate : Measurable (fun ω =>
      if AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω) then
        ⨆ z : Plane, edist z (f ω z) else (0 : ENNReal)) :=
    Measurable.ite hA hd measurable_const
  have hm := hdgate.add hc
  convert hm using 1
  funext ω
  by_cases h : AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω)
  · simp only [Pi.add_apply, h, ite_true, distortion]
  · simp only [Pi.add_apply, h, ite_false, zero_add]

end ReflectedGMS.GMS.ValidCodeSet
