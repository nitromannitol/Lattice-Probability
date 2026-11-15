import LatticeProb.LQG.PeanosphereGridArcMarginal
import LatticeProb.Topology.GridFrontierArcWindows

/-! # Ordered frontier arcs through the contour marginal -/

set_option autoImplicit false

open MeasureTheory Set Function
open scoped unitInterval

namespace MatedCRTHarmonic.RouteM

/-- A source grid-arc event transfers through the contour marginal to ordered
windows for every continuous contour coordinate on one target event. -/
theorem ae_ordered_shared_frontier_arc_of_marginal
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure (MatedCRT.Path2 × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (w : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    (hw : Measurable w) (hlaw : P.map w = μ.map Prod.fst)
    (F : ι → MatedCRT.Path2 → ℝ → ℝ)
    (hF : ∀ k p, Continuous (F k p))
    {A : Set (MatedCRT.Path2 × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, Peanosphere p.1 p.2 ∧
      ∀ k : ι, ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j →
        let ε : ℝ := 1 / n
        max (sInf (F k p.1 '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
          (sInf (F k p.1 '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
          sInf (F k p.1 '' Icc (ε * i) (ε * ((j : ℝ) - 1))) →
        ∃ q : C(unitInterval, ℂ), Injective q ∧
          (∀ t, q t ∈ frontier (p.2 '' Icc (ε * ((i : ℝ) - 1)) (ε * i))) ∧
          (∀ t, q t ∈ frontier (p.2 '' Icc (ε * ((j : ℝ) - 1)) (ε * j))))
    (htarget : ∀ᵐ ω ∂P, Peanosphere (w ω) (η ω))
    (hfront : ∀ᵐ ω ∂P, ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      η ω '' Icc a b ∩ η ω '' Icc c d =
        frontier (η ω '' Icc a b) ∩ frontier (η ω '' Icc c d)) :
    ∀ᵐ ω ∂P, ∀ k : ι, ∀ a b c d : ℝ, a < b → b ≤ c → c < d →
      max (sInf (F k (w ω) '' Icc a b)) (sInf (F k (w ω) '' Icc c d)) <
        sInf (F k (w ω) '' Icc b c) →
      ∃ q : C(unitInterval, ℂ), Injective q ∧
        (∀ t, q t ∈ frontier (η ω '' Icc a b)) ∧
        (∀ t, q t ∈ frontier (η ω '' Icc c d)) := by
  let R : MatedCRT.Path2 → ℕ → ℤ → ℤ → Prop := fun p n i j =>
    ∃ k : ι, let ε : ℝ := 1 / n
      max (sInf (F k p '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
        (sInf (F k p '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
        sInf (F k p '' Icc (ε * i) (ε * ((j : ℝ) - 1)))
  have hgrid := ae_grid_shared_frontier_arc_of_marginal μ P w η hw hlaw R hA hfull
    (fun p hp => ⟨(hsource p hp).1, by
      intro n hn i j hij hR
      obtain ⟨k, hk⟩ := hR
      exact (hsource p hp).2 k n hn i j hij hk⟩) htarget
  filter_upwards [hgrid, hfront] with ω hg hf
  intro k a b c d hab hbc hcd hgap
  apply LatticeProb.shared_frontier_arc_of_grid_frontier_arcs (η ω) (F k (w ω))
    (η ω).continuous (hF k (w ω)) hf ?_ hab hbc hcd hgap
  intro n hn i j hij ε hmin
  exact hg n hn i j hij ⟨k, hmin⟩

end MatedCRTHarmonic.RouteM
