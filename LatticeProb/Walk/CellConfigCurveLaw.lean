import LatticeProb.Topology.UnboundedRayAECoupledTimeChangeLaw
import LatticeProb.Walk.CellConfigConstantStepComparison
import LatticeProb.Walk.ScaledCellWalkSupport

/-! # Curve laws of cell walk interpolations -/

set_option autoImplicit false

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigWalk

open UnboundedRayIntervalIntegrand UnboundedRayCurveSpace

noncomputable section

private theorem unbounded_scaled_constantStep
    (H : CellConfig) (hH : H.IsCellConfiguration) (ω : ℕ → H.cells)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ ((K.1 : Cell) : Set Plane))
    (hω : (Set.range ω).Infinite) {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) :
    ¬ Bornology.IsBounded (Set.range
      (ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n)))) := by
  intro hb
  have hscaled : Bornology.IsBounded (Set.range (fun n => (ε : ℝ) • p (ω n))) := by
    apply hb.subset
    rintro _ ⟨n, rfl⟩
    refine ⟨ConstantStepInterpolation.knot m n, ?_⟩
    change ConstantStepInterpolation.path m (fun n => (ε : ℝ) • p (ω n))
      (ConstantStepInterpolation.knot m n) = _
    exact ConstantStepInterpolation.path_knot hm _ n
  have hne : (ε : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hε)
  have hunscaled : Bornology.IsBounded (Set.range (fun n => p (ω n))) := by
    apply (hscaled.smul₀ (ε : ℝ)⁻¹).subset
    rintro _ ⟨n, rfl⟩
    refine ⟨(ε : ℝ) • p (ω n), ⟨n, rfl⟩, ?_⟩
    simp [smul_smul, hne]
  exact (unbounded_range_representatives_of_infinite_range_cells H hH ω
    (fun n => p (ω n)) (fun n => hp (ω n)) hω) hunscaled

/-- On a recurrent line-connected cell configuration, holding-time and
constant-step interpolations of the same walk have the same curve law. -/
theorem curveLaw_constantStep_eq_interpolatedWalk
    (H : CellConfig) (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    (hrec : H.Recurrent) (hpos : ∀ K, 0 < H.holding K)
    {K : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K Q)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ ((K.1 : Cell) : Set Plane))
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) :
    let X : (ℕ → H.cells) → Path 2 := fun ω =>
      ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
    let Y : (ℕ → H.cells) → Path 2 := H.interpolatedWalk p ε
    let : IsProbabilityMeasure (Q.map X) := by
      let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
      let : IsProbabilityMeasure Q := hQ.1
      apply (Measure.isProbabilityMeasure_map_iff ?_).2 inferInstance
      apply (measurable_constantStepPath _ ?_ m).aemeasurable
      apply Measurable.of_eval
      intro n
      exact (measurable_const : Measurable (fun _ : ℕ → H.cells => (ε : ℝ))).smul
        ((measurable_of_countable p).comp (measurable_pi_apply n))
    let : IsProbabilityMeasure (Q.map Y) := by
      let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
      let : IsProbabilityMeasure Q := hQ.1
      exact (Measure.isProbabilityMeasure_map_iff
        (aemeasurable_interpolatedWalk_of_recurrent hrec hpos hQ p ε)).2 inferInstance
    ∃ hx : ∀ᵐ (f : Path 2) ∂(Q.map X), ¬ Bornology.IsBounded (Set.range f),
    ∃ hy : ∀ᵐ (f : Path 2) ∂(Q.map Y), ¬ Bornology.IsBounded (Set.range f),
      curveLaw (Q.map X) hx = curveLaw (Q.map Y) hy := by
  let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
  let : IsProbabilityMeasure Q := hQ.1
  let X : (ℕ → H.cells) → Path 2 := fun ω =>
    ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
  let Y : (ℕ → H.cells) → Path 2 := H.interpolatedWalk p ε
  have hpmeas : Measurable (fun ω : ℕ → H.cells => fun n => (ε : ℝ) • p (ω n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_const : Measurable (fun _ : ℕ → H.cells => (ε : ℝ))).smul
      ((measurable_of_countable p).comp (measurable_pi_apply n))
  have hX : AEMeasurable X Q := (measurable_constantStepPath _ hpmeas m).aemeasurable
  have hY : AEMeasurable Y Q :=
    aemeasurable_interpolatedWalk_of_recurrent hrec hpos hQ p ε
  have hXu : ∀ᵐ ω ∂Q, ¬ Bornology.IsBounded (Set.range (X ω)) := by
    filter_upwards [ae_infinite_range_of_lineConnected H hH hL hQ] with ω hω
    exact unbounded_scaled_constantStep H hH ω p hp hω hε hm
  have hc : ∀ᵐ ω ∂Q, ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t, Y ω t = X ω (φ t) := by
    filter_upwards [ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ] with ω hω
    obtain ⟨φ, _, hφ⟩ :=
      CellConfigInterpolation.exists_orderIso_interpolatedWalk_eq_constantStep H p ω hpos hω hε hm
    exact ⟨φ, hφ⟩
  exact curveLaw_eq_of_ae_timeChange_of_aemeasurable Q X Y hX hY hXu hc

end
end LatticeProb.CellConfigWalk
