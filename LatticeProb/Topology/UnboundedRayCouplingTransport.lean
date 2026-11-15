import LatticeProb.Topology.UnboundedRayCoupledTimeChangeLaw

/-! # Transport of local curve laws through couplings -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand

noncomputable section

/-- Probability laws coupled by an almost surely increasing bijective change of
clock have identical local curve laws when the first has unbounded support. -/
theorem curveLaw_eq_of_coupling_timeChange {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ ν : Measure (Path d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ (f : Path d) ∂μ, ¬ Bornology.IsBounded (Set.range f))
    (X Y : Ω → Path d) (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : P.map X = μ) (hYlaw : P.map Y = ν)
    (hclock : ∀ᵐ ω ∂P, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y ω t = X ω (φ t)) :
    ∃ hν : ∀ᵐ (f : Path d) ∂ν, ¬ Bornology.IsBounded (Set.range f),
      curveLaw μ hμ = curveLaw ν hν := by
  have hXu : ∀ᵐ ω ∂P, ¬ Bornology.IsBounded (Set.range (X ω)) := by
    apply (ae_map_iff hX.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).1
    rw [hXlaw]
    exact hμ
  obtain ⟨hx, hy, hcurve⟩ := curveLaw_eq_of_ae_timeChange P X Y hX hY hXu hclock
  subst μ
  subst ν
  exact ⟨hy, hcurve⟩

end
end LatticeProb.UnboundedRayCurveSpace
