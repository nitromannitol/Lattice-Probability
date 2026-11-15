import LatticeProb.Prob.BrownianRestrictedEndpointExit

/-! # Uniform comparison of endpoint exit probabilities -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped ENNReal Topology

namespace LatticeProb.ParentBlock

/-- For a covered measurable set with a common null frontier, nearby starting
parameters have uniformly close endpoint exit probabilities. -/
theorem brownian_ball_endpoint_exit_bounds
    {J : Type*} [Fintype J]
    (center : J → Euc 2) (radius : J → ℝ)
    (c : ℂ) {S : ℝ} (hS : 0 < S)
    (hcenter : ∀ j, Complex.orthonormalBasisOneI.repr.symm (center j) ∈ closedSquare c S)
    (hradius : ∀ j, radius j ≤ S)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (x : ∀ j, P j → Euc 2) (hx : ∀ j z, x j z ∈ ball (center j) (radius j))
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc 2))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc 2))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc 2)) =
      (stoppedBrownianLaw (ball (center j) (radius j)) (x j z) ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (ν j (p j n v) : Measure (Euc 2)) < ε)
    (outer : Set (Euc 2)) (houter : MeasurableSet outer)
    (hcovered : outer ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S)
    (b : ℝ) (hb : 0 < b)
    (hnullOuter : ∀ j z, (ν j z : Measure (Euc 2)) (frontier outer) = 0)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [∀ n, MeasurableSpace (Option (ParentDyadicIndex n))] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
      dist (p j k v) z ≤ δ →
        (μ j k v : Measure (Euc 2)) outerᶜ ≤
            (ν j z : Measure (Euc 2)) outerᶜ + ENNReal.ofReal b ∧
          (ν j z : Measure (Euc 2)) outerᶜ ≤
            (μ j k v : Measure (Euc 2)) outerᶜ + ENNReal.ofReal b := by
  obtain ⟨n, hn⟩ := (eventually_brownian_ball_dyadic_restricted_endpoint_exit_bounds
    center radius c hS hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP
    outer houter hcovered b hb hnullOuter).exists
  obtain ⟨m, E, choice, hd, hcover, hm, hbnd, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, δ, hδ, hbound⟩ := hn
  exact ⟨δ, hδ, hbound⟩

end LatticeProb.ParentBlock
