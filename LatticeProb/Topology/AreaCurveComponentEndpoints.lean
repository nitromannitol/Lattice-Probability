import LatticeProb.Topology.RandomCurveComponentEndpoints
import LatticeProb.Analysis.VagueLimitCompactMass
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.PushArea

/-! # Endpoints of components of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- The endpoints of a selected component have measurable versions when the
curve is surjective, rational interval images have the prescribed mass, and the
fixed-time interior and component-image properties hold almost surely. -/
theorem exists_measurable_endpoints_of_curve_component_rat_mass
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [SigmaFinite P] (B : ι → Set ℂ)
    (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ) (x : Ω → ℂ)
    (s t : ℝ) (a b : Ω → ℝ)
    (hf : Measurable f) (hx : Measurable x)
    (hopen : ∀ i, IsOpen (B i)) (hconn : ∀ i, IsPreconnected (B i))
    (hbasis : ∀ (V : Set ℂ), IsOpen V → ∀ z ∈ V, ∃ i, z ∈ B i ∧ B i ⊆ V)
    (hfixed : ∀ u ∈ Ioo s t, ∀ᵐ ω ∂P, f ω u ∈ interior (f ω '' Icc s t))
    (harea : ∀ᵐ ω ∂P, Function.Surjective (f ω) ∧
      ∀ p q : ℚ, p ≤ q → μ ω (f ω '' Icc (p : ℝ) q) = ENNReal.ofReal ((q : ℝ) - p))
    (hcomponent : ∀ᵐ ω ∂P,
      let U := connectedComponentIn (interior (f ω '' Icc s t)) (x ω)
      U.Nonempty ∧ f ω '' Icc (a ω) (b ω) = closure U) :
    ∃ a' b' : Ω → ℝ, Measurable a' ∧ Measurable b' ∧
      (∀ᵐ ω ∂P, a' ω = a ω ∧ b' ω = b ω) := by
  have hfull : ∀ᵐ ω ∂P, Function.Surjective (f ω) ∧
      ∀ u v : ℝ, μ ω (f ω '' Icc u v) = volume (Icc u v) := by
    filter_upwards [harea] with ω hω
    refine ⟨hω.1, ?_⟩
    intro u v
    by_cases huv : u ≤ v
    · rw [Real.volume_Icc]
      exact VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2 huv
    · simp [Icc_eq_empty huv]
  apply exists_measurable_endpoints_of_curve_component_mass P B f μ x s t a b
    hf hx hopen hconn hbasis hfixed
  · filter_upwards [harea] with ω hω
    exact (MatedCRTHarmonic.GMS4cM.eq_map_volume (f ω).continuous hω.1
      (fun u v huv => VagueLimit.measure_image_Icc_eq_ofReal_of_rat hω.2 huv)).symm
  · filter_upwards [hfull] with ω hω
    exact hω.2 s t
  · filter_upwards [hfull, hcomponent] with ω hω hc
    exact ⟨hc.1, hc.2, hω.2 (a ω) (b ω)⟩

end LatticeProb
