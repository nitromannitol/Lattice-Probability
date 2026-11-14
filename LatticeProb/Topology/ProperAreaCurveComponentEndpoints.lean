import LatticeProb.Topology.AreaCurveComponentEndpoints
import LatticeProb.Topology.ProperAreaCurveFrontier

/-! # Endpoints of components of proper area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- The endpoints of a selected interior component have measurable versions if
its interval image is its closure, and the curve is proper, surjective, and
area-parametrized. -/
theorem exists_measurable_endpoints_of_proper_curve_component_rat_mass
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (B : ι → Set ℂ)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (x : Ω → ℂ)
    (s t : ℝ) (a b : Ω → ℝ)
    (hf : Measurable f) (hx : Measurable x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hst : s < t)
    (harea : ∀ᵐ ω ∂P, IsProperMap (f ω) ∧ Function.Surjective (f ω) ∧
      ∀ p q : ℚ, p ≤ q → μ ω (f ω '' Icc (p : ℝ) q) = ENNReal.ofReal ((q : ℝ) - p))
    (hcomponent : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  apply exists_measurable_endpoints_of_ae_curve_component_visits P B f x
    isCompact_Icc hf hx a b hopen hconn hbasis
  filter_upwards [harea, hcomponent] with ω hω hc
  have hmass : ∀ u v : ℝ, μ ω (f ω '' Icc u v) = volume (Icc u v) := by
    intro u v
    by_cases huv : u ≤ v
    · rw [Real.volume_Icc]
      exact VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2.2 huv
    · simp [Icc_eq_empty huv]
  have hmap : Measure.map (f ω) volume = μ ω :=
    (MatedCRTHarmonic.GMS4cM.eq_map_volume (f ω).continuous hω.2.1
      (fun u v huv => VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2.2 huv)).symm
  have hfront : μ ω (frontier (f ω '' Icc s t)) = 0 :=
    measure_frontier_image_Icc_eq_zero_of_proper (f ω) (μ ω) (f ω).continuous
      hω.1 hω.2.1
      (fun u v huv => VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2.2 huv.le) hst
  have hU : IsOpen (connectedComponentIn (interior (f ω '' Icc s t)) (x ω)) :=
    isOpen_interior.connectedComponentIn
  have hzero : μ ω (frontier (connectedComponentIn (interior (f ω '' Icc s t)) (x ω))) = 0 :=
    measure_frontier_component_interior_eq_zero
      (isCompact_Icc.image (f ω).continuous).isClosed (μ ω) hfront (x ω)
  refine ⟨hU, hc.1, hc.2, ?_⟩
  exact ae_visit_open_eq_interval (f ω) (μ ω) _ (a ω) (b ω)
    (f ω).continuous.measurable hmap hU hzero hc.2 (hmass (a ω) (b ω))

end LatticeProb
