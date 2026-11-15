import LatticeProb.Topology.AreaCurveRegularClosed

/-! # Interior visits of area-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Almost every time in a nondegenerate segment of a proper surjective
area-parametrized curve visits the interior of that segment's image. -/
theorem ae_mem_interior_image_Icc_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ u ∂volume, u ∈ Icc a b → η u ∈ interior (η '' Icc a b) := by
  have hfront := measure_frontier_image_Icc_eq_zero_of_proper η μ hη hp hs harea hab
  have hae := interior_ae_eq_of_null_frontier hfront
  rw [← hmap] at hae
  have hae' := ae_of_ae_map hη.measurable.aemeasurable hae
  filter_upwards [hae'] with u hu huI
  exact hu.mpr ⟨u, huI, rfl⟩

/-- If the segment image has connected interior, almost every time in the
segment selects a component whose closure is the whole image. -/
theorem ae_component_closure_eq_image_Icc_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b : ℝ} (hab : a < b)
    (hconn : IsConnected (interior (η '' Icc a b))) :
    ∀ᵐ u ∂volume, u ∈ Icc a b →
      closure (connectedComponentIn (interior (η '' Icc a b)) (η u)) =
        η '' Icc a b := by
  filter_upwards [ae_mem_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hab]
    with u hu huI
  rw [hconn.isPreconnected.connectedComponentIn (hu huI)]
  exact closure_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hab

end LatticeProb
