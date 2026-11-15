import LatticeProb.LQG.PeanosphereContourFibers
import LatticeProb.Prob.AnalyticWitnessTransfer
import LatticeProb.Topology.PolishContinuousMap

/-! # Transfer of grid arcs through the contour marginal -/

set_option autoImplicit false

open MeasureTheory Set Function
open scoped unitInterval

namespace MatedCRTHarmonic.RouteM

/-- Shared frontier arcs for every reciprocal grid transfer through the contour
marginal when both source and target curves have the Peanosphere structure. -/
theorem ae_grid_shared_frontier_arc_of_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (MatedCRT.Path2 × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (w : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    (hw : Measurable w) (hlaw : P.map w = μ.map Prod.fst)
    (R : MatedCRT.Path2 → ℕ → ℤ → ℤ → Prop)
    {A : Set (MatedCRT.Path2 × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, Peanosphere p.1 p.2 ∧
      ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j → R p.1 n i j →
        let ε : ℝ := 1 / n
        ∃ q : C(unitInterval, ℂ), Injective q ∧
          (∀ t, q t ∈ frontier (p.2 '' Icc (ε * ((i : ℝ) - 1)) (ε * i))) ∧
          (∀ t, q t ∈ frontier (p.2 '' Icc (ε * ((j : ℝ) - 1)) (ε * j))))
    (htarget : ∀ᵐ ω ∂P, Peanosphere (w ω) (η ω)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j → R (w ω) n i j →
      let ε : ℝ := 1 / n
      ∃ q : C(unitInterval, ℂ), Injective q ∧
        (∀ t, q t ∈ frontier (η ω '' Icc (ε * ((i : ℝ) - 1)) (ε * i))) ∧
        (∀ t, q t ∈ frontier (η ω '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) := by
  have : PolishSpace MatedCRT.Path2 := LatticeProb.polishSpace_continuousMap ℝ (ℝ × ℝ)
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  filter_upwards [LatticeProb.ae_exists_witness_of_marginal_law μ P w hw hlaw hA hfull,
    htarget] with ω hwitness hp
  obtain ⟨ξ, hξ⟩ := hwitness
  obtain ⟨hξp, hgrid⟩ := hsource (w ω, ξ) hξ
  intro n hn i j hij hR
  exact (LatticeProb.Peanosphere.shared_frontier_arc_iff hξp hp
    (Icc ((1 / (n : ℝ)) * ((i : ℝ) - 1)) ((1 / (n : ℝ)) * i))
    (Icc ((1 / (n : ℝ)) * ((j : ℝ) - 1)) ((1 / (n : ℝ)) * j))).2
      (hgrid n hn i j hij hR)

end MatedCRTHarmonic.RouteM
