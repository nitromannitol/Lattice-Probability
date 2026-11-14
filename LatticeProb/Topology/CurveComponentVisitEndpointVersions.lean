import LatticeProb.Topology.MeasurableCurveComponent
import LatticeProb.Topology.ComponentVisitEndpointVersions
import LatticeProb.Topology.ContinuousMapBorel

/-! # Endpoints of visits to components of random curve images -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A continuous random curve visits the selected component of the interior of its
compact image at a fixed time in a measurable event. -/
theorem measurableSet_curve_mem_component_interior_image
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (B : ι → Set E) (f : Ω → C(ℝ, E)) (x : Ω → E) {K : Set ℝ}
    (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x) (t : ℝ)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V) :
    MeasurableSet {ω | f ω t ∈ connectedComponentIn (interior (f ω '' K)) (x ω)} := by
  exact measurableSet_mem_connectedComponentIn_interior_image B f x (fun ω => f ω t)
    hK hf hx ((ContinuousMap.measurable_eval t).comp hf) hopen hconn hbasis

/-- Under the almost-everywhere interval-visit identity, the endpoints of the
selected component have measurable versions. -/
theorem exists_measurable_endpoints_of_ae_curve_component_visits
    {Ω E ι : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E] [PerfectSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] [Countable ι]
    (P : Measure Ω) (B : ι → Set E) (f : Ω → C(ℝ, E)) (x : Ω → E)
    {K : Set ℝ} (hK : IsCompact K) (hf : Measurable f) (hx : Measurable x)
    (a b : Ω → ℝ)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set E), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hgood : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' K)) (x ω)
      IsOpen U ∧ U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U ∧
      ∀ᵐ t ∂volume, f ω t ∈ U ↔ t ∈ Ioo (a ω) (b ω)) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  apply exists_measurable_endpoints_of_ae_open_curve_visits P (fun ω => f ω)
    (fun ω => connectedComponentIn (interior (f ω '' K)) (x ω)) a b
  · intro q
    exact measurableSet_curve_mem_component_interior_image B f x hK hf hx q hopen hconn hbasis
  · filter_upwards [hgood] with ω hω
    exact ⟨(f ω).continuous, hω⟩

end LatticeProb
