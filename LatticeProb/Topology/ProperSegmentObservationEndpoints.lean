import LatticeProb.Topology.ProperAreaCurveComponentEndpoints
import LatticeProb.Topology.AreaCurveIntervalContainment
import LatticeProb.Topology.SegmentObservationEndpointVersions

/-! # Component endpoints from observations of a proper area curve -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- The endpoints of a selected component of a proper area-parametrized curve
have versions measurable from observations of the segment containing it, provided
that the component closure is the image of the endpoint interval. -/
theorem exists_observable_endpoints_of_proper_curve_component
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (obs : MeasurableSpace Ω) (P : Measure Ω) (B : ι → Set ℂ)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (x : Ω → ℂ)
    (s t : ℝ) (a b : Ω → ℝ) (hst : s < t)
    (hf : ∀ r ∈ Icc s t, @Measurable Ω ℂ obs _ (fun ω => f ω r))
    (hx : @Measurable Ω ℂ obs _ x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (harea : ∀ᵐ ω ∂P, IsProperMap (f ω) ∧ Function.Surjective (f ω) ∧
      ∀ p q : ℚ, p ≤ q → μ ω (f ω '' Icc (p : ℝ) q) = ENNReal.ofReal ((q : ℝ) - p))
    (hcomponent : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U) :
    ∃ a' b' : Ω → ℝ, @Measurable Ω ℝ obs _ a' ∧ @Measurable Ω ℝ obs _ b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  apply exists_observable_endpoints_of_segment_observations obs P B f x s t hst.le a b
    hf hx hopen hconn hbasis
  filter_upwards [harea, hcomponent] with ω hω hc
  let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
  have hmass (u v : ℝ) (huv : u < v) :
      μ ω (f ω '' Icc u v) = ENNReal.ofReal (v - u) :=
    VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2.2 huv.le
  have hmap : Measure.map (f ω) volume = μ ω :=
    (MatedCRTHarmonic.GMS4cM.eq_map_volume (f ω).continuous hω.2.1
      (fun u v huv => VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2.2 huv)).symm
  have hfront : μ ω (frontier (f ω '' Icc s t)) = 0 :=
    measure_frontier_image_Icc_eq_zero_of_proper (f ω) (μ ω) (f ω).continuous
      hω.1 hω.2.1 (fun u v huv => hmass u v huv) hst
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have hzero : μ ω (frontier U) = 0 :=
    measure_frontier_component_interior_eq_zero
      (isCompact_Icc.image (f ω).continuous).isClosed (μ ω) hfront (x ω)
  have hab : a ω < b ω :=
    interval_lt_of_image_eq_closure_open (f ω) U (a ω) (b ω) hU hc.1 hc.2
  have hsub : f ω '' Icc (a ω) (b ω) ⊆ f ω '' Icc s t := by
    rw [hc.2]
    exact closure_minimal
      ((connectedComponentIn_subset _ _).trans interior_subset)
      (isCompact_Icc.image (f ω).continuous).isClosed
  have hbounds := Icc_subset_of_area_curve_image_subset (f ω) (μ ω)
    (f ω).continuous hmass hab hst hsub
  refine ⟨(hbounds ⟨le_rfl, hab.le⟩).1, hab, (hbounds ⟨hab.le, le_rfl⟩).2, ?_⟩
  apply ae_visit_open_eq_interval (f ω) (μ ω) U (a ω) (b ω)
    (f ω).continuous.measurable hmap hU hzero hc.2
  rw [hmass _ _ hab, Real.volume_Icc]

end LatticeProb
