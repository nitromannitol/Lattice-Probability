import LatticeProb.ReflectedGMS.GMS.TypedConductanceMeasurable
import LatticeProb.ReflectedGMS.GMS.VariableRadiusCodedAdmissible

/-! # Measurability of admissibility-gated conductance discrepancies -/

set_option autoImplicit false

open Set Topology
open scoped Classical

namespace ReflectedGMS.GMS.ValidCodeSet

open Code CellConfig

/-- The decoded conductance discrepancy, set to zero outside the admissible event,
is measurable for measurable good codes and homeomorphism coordinates. -/
theorem measurable_admissible_decoded_conductance_iSup
    {Ω : Type*} [MeasurableSpace Ω] (r : Ω → ℝ) (x y : Ω → RawCode)
    (f : Ω → Plane ≃ₜ Plane)
    (hr : Measurable r) (hx : Measurable x) (hy : Measurable y)
    (hf : Measurable fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)))
    (hfi : Measurable fun ω =>
      (⟨(f ω).symm, (f ω).symm.continuous⟩ : C(Plane, Plane)))
    (hgx : ∀ ω, IsGoodCode (x ω)) (hgy : ∀ ω, IsGoodCode (y ω)) :
    Measurable fun ω =>
      if AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω) then
        ⨆ (C ∈ (decodeConfig (x ω)).restrict (Metric.ball 0 (r ω)))
          (C' ∈ (decodeConfig (x ω)).restrict (Metric.ball 0 (r ω)))
          (_ : (decodeConfig (x ω)).Adj C C'),
          ENNReal.ofReal |(decodeConfig (x ω)).c C C' -
            (decodeConfig (y ω)).c (mapCell (f ω) C) (mapCell (f ω) C')|
      else 0 := by
  classical
  have hA := measurableSet_admissibleAt_decodeConfig_variable_radius
    r x y f hx hy hr hgx hgy hf hfi
  have hm : Measurable (fun ω =>
      if AdmissibleAt (decodeConfig (x ω)) (decodeConfig (y ω)) (r ω) (f ω) then
        indexedConductanceDiscrepancy (r ω) (x ω) (y ω)
          (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane)) else (0 : ENNReal)) :=
    Measurable.ite hA
    (measurable_indexedConductanceDiscrepancy r x y
      (fun ω => (⟨f ω, (f ω).continuous⟩ : C(Plane, Plane))) hr hx hy hf)
    (measurable_const : Measurable (fun _ : Ω => (0 : ENNReal)))
  convert hm using 1
  ext ω
  split_ifs with h
  · exact conductance_iSup_eq_indexedConductanceDiscrepancy _ _ (hgx ω) (hgy ω)
      _ _ h.1
  · rfl

end ReflectedGMS.GMS.ValidCodeSet
