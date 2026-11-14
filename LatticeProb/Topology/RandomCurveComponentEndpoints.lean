import LatticeProb.Topology.RandomCurveComponentFrontier
import LatticeProb.Topology.ComponentVisitIdentity
import LatticeProb.Topology.CurveComponentVisitEndpointVersions
import Mathlib.Topology.Connected.LocallyConnected

/-! # Measurable endpoints of random curve components -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The endpoints of a selected component admit measurable versions when the
curve is measure-parametrized, its fixed-time visits are interior almost surely,
and the component has the stated interval image and mass. -/
theorem exists_measurable_endpoints_of_curve_component_mass
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [SigmaFinite P] (B : ι → Set ℂ)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (x : Ω → ℂ)
    (s t : ℝ) (a b : Ω → ℝ)
    (hf : Measurable f) (hx : Measurable x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hfixed : ∀ u ∈ Ioo s t, ∀ᵐ ω ∂P, f ω u ∈ interior (f ω '' Icc s t))
    (hmap : ∀ᵐ ω ∂P, Measure.map (f ω) volume = μ ω)
    (hsegment : ∀ᵐ ω ∂P, μ ω (f ω '' Icc s t) = volume (Icc s t))
    (hcomponent : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U ∧
        μ ω (f ω '' Icc (a ω) (b ω)) = volume (Icc (a ω) (b ω))) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  have hfront := ae_measure_frontier_curve_components_eq_zero P B f μ s t
    hf hopen hbasis hfixed hmap hsegment
  apply exists_measurable_endpoints_of_ae_curve_component_visits P B f x
    isCompact_Icc hf hx a b hopen hconn hbasis
  filter_upwards [hfront, hmap, hcomponent] with ω hzero hm hc
  have hU : IsOpen (connectedComponentIn (interior (f ω '' Icc s t)) (x ω)) :=
    isOpen_interior.connectedComponentIn
  refine ⟨hU, hc.1, hc.2.1, ?_⟩
  exact ae_visit_open_eq_interval (f ω) (μ ω) _ (a ω) (b ω)
    (f ω).continuous.measurable hm hU (hzero (x ω)) hc.2.1 hc.2.2

end LatticeProb
