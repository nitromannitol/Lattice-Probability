import LatticeProb.Topology.AreaCurveSimultaneousInterior
import LatticeProb.Topology.AreaCurveRationalConnected

/-! # Simultaneous component visits of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- If every rational segment has connected interior, almost every time selects
    the whole segment as the closure of its interior component, simultaneously
    for all strictly containing segments. -/
theorem ae_component_closure_all_image_Icc_of_rational_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    (hconn : ∀ (p q : ℚ), (p : ℝ) < (q : ℝ) →
      IsConnected (interior (η '' Icc (p : ℝ) (q : ℝ)))) :
    ∀ᵐ u ∂volume, ∀ a b : ℝ, a < u → u < b →
      (connectedComponentIn (interior (η '' Icc a b)) (η u)).Nonempty ∧
      closure (connectedComponentIn (interior (η '' Icc a b)) (η u)) = η '' Icc a b := by
  have hall := connected_interior_image_Icc_of_rational_of_proper_area_curve
    η μ hη hp hs hmap harea hconn
  filter_upwards [ae_mem_interior_all_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea]
    with u hu
  intro a b hau hub
  have hmem := hu a b hau hub
  obtain ⟨hc, hclosed⟩ := hall a b (hau.trans hub)
  refine ⟨⟨η u, mem_connectedComponentIn hmem⟩, ?_⟩
  rw [hc.isPreconnected.connectedComponentIn hmem]
  exact hclosed

end LatticeProb
