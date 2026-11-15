import LatticeProb.Prob.SourceSampleWitness
import LatticeProb.LQG.PeanosphereOrderedArcMarginal

/-! # Ordered frontier arcs from source samples -/

set_option autoImplicit false

open MeasureTheory Set Function
open scoped unitInterval

namespace MatedCRTHarmonic.RouteM

/-- A simultaneous grid-arc property on source samples transfers to ordered
windows along the common contour law. The source curve need not be measurable. -/
theorem ae_ordered_shared_frontier_arc_of_source_samples
    {S Ω ι : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω]
    (ν : Measure S) [IsFiniteMeasure ν] (P : Measure Ω)
    (f : S → MatedCRT.Path2) (ξ : S → C(ℝ, ℂ))
    (w : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    (hf : Measurable f) (hw : Measurable w) (hlaw : P.map w = ν.map f)
    (F : ι → MatedCRT.Path2 → ℝ → ℝ)
    (hF : ∀ k p, Continuous (F k p))
    (hsource : ∀ᵐ s ∂ν, Peanosphere (f s) (ξ s) ∧
      ∀ k : ι, ∀ n : ℕ, 0 < n → ∀ i j : ℤ, i + 1 < j →
        let ε : ℝ := 1 / n
        max (sInf (F k (f s) '' Icc (ε * ((i : ℝ) - 1)) (ε * i)))
          (sInf (F k (f s) '' Icc (ε * ((j : ℝ) - 1)) (ε * j))) <
          sInf (F k (f s) '' Icc (ε * i) (ε * ((j : ℝ) - 1))) →
        ∃ q : C(unitInterval, ℂ), Injective q ∧
          (∀ t, q t ∈ frontier (ξ s '' Icc (ε * ((i : ℝ) - 1)) (ε * i))) ∧
          (∀ t, q t ∈ frontier (ξ s '' Icc (ε * ((j : ℝ) - 1)) (ε * j))))
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
  have : PolishSpace MatedCRT.Path2 := LatticeProb.polishSpace_continuousMap ℝ (ℝ × ℝ)
  filter_upwards [LatticeProb.ae_exists_source_witness_of_same_law ν P f w hf hw hlaw hsource,
    htarget, hfront] with ω hwitness hp hfrontω
  obtain ⟨s, hs, hpeano, hgrid⟩ := hwitness
  rw [hs] at hpeano hgrid
  intro k a b c d hab hbc hcd hgap
  apply LatticeProb.shared_frontier_arc_of_grid_frontier_arcs (η ω) (F k (w ω))
    (η ω).continuous (hF k (w ω)) hfrontω ?_ hab hbc hcd hgap
  intro n hn i j hij ε hmin
  exact (LatticeProb.Peanosphere.shared_frontier_arc_iff hpeano hp
    (Icc (ε * ((i : ℝ) - 1)) (ε * i))
    (Icc (ε * ((j : ℝ) - 1)) (ε * j))).2 (hgrid k n hn i j hij hmin)

end MatedCRTHarmonic.RouteM
