import LatticeProb.Topology.UnboundedRayCoupledTimeChangeLaw

/-! # Almost-everywhere measurable coupled paths -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

noncomputable section

local instance {d : ℕ} : MeasurableSpace (UnboundedRayCurveSpace d) := borel _
local instance {d : ℕ} : BorelSpace (UnboundedRayCurveSpace d) := ⟨rfl⟩

/-- Almost-everywhere measurable coupled paths related by increasing bijective
clocks have the same local curve law. -/
theorem curveLaw_eq_of_ae_timeChange_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (X Y : Ω → Path d) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXu : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (X ω)))
    (hclock : ∀ᵐ ω ∂P, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y ω t = X ω (φ t)) :
    let : IsProbabilityMeasure (P.map X) :=
      (Measure.isProbabilityMeasure_map_iff hX).2 inferInstance
    let : IsProbabilityMeasure (P.map Y) :=
      (Measure.isProbabilityMeasure_map_iff hY).2 inferInstance
    ∃ hx : ∀ᵐ (f : Path d) ∂(P.map X), ¬ Bornology.IsBounded (Set.range f),
    ∃ hy : ∀ᵐ (f : Path d) ∂(P.map Y), ¬ Bornology.IsBounded (Set.range f),
      curveLaw (P.map X) hx = curveLaw (P.map Y) hy := by
  let X' := hX.mk X
  let Y' := hY.mk Y
  have hu : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (X' ω)) := by
    filter_upwards [hXu, hX.ae_eq_mk] with ω hu he
    change X ω = X' ω at he
    rw [← he]
    exact hu
  have hc : ∀ᵐ ω ∂P, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y' ω t = X' ω (φ t) := by
    filter_upwards [hclock, hX.ae_eq_mk, hY.ae_eq_mk] with ω hc hx hy
    change X ω = X' ω at hx
    change Y ω = Y' ω at hy
    rw [← hx, ← hy]
    exact hc
  obtain ⟨hx, hy, heq⟩ := curveLaw_eq_of_ae_timeChange P X' Y'
    hX.measurable_mk hY.measurable_mk hu hc
  have hmapX : P.map X = P.map X' := Measure.map_congr hX.ae_eq_mk
  have hmapY : P.map Y = P.map Y' := Measure.map_congr hY.ae_eq_mk
  rw [← hmapX] at hx
  rw [← hmapY] at hy
  refine ⟨hx, hy, ?_⟩
  simpa only [hmapX, hmapY] using heq

end
end LatticeProb.UnboundedRayCurveSpace
