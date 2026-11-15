import LatticeProb.Prob.BrownianRestrictedSelectorCoupling
import LatticeProb.Prob.DyadicNullNeighborhood

/-! # Restricted selectors with small boundary error -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped ENNReal Topology

namespace LatticeProb.ParentBlock

/-- A sufficiently fine dyadic scale gives uniformly small boundary error for
restricted Brownian endpoint selectors when the outer frontier is null. -/
theorem eventually_brownian_ball_dyadic_restricted_selector_small_boundary
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
    (outer : Set (Euc 2)) (η : ℝ≥0∞) (hη : 0 < η)
    (hnullOuter : ∀ j z, (ν j z : Measure (Euc 2)) (frontier outer) = 0)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [∀ n, MeasurableSpace (Option (ParentDyadicIndex n))] :
    ∀ᶠ n : ℕ in atTop, ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S) ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < (2 * S / (2 : ℝ) ^ n) / 2) ∧
      (∀ j i z, (ν j z : Measure (Euc 2)) (frontier (E i)) = 0) ∧
      (∀ j z q, (ν j z : Measure (Euc 2))
        (frontier (cellSelector E choice ⁻¹' {q})) = 0) ∧
      Measurable (cellSelector E choice) ∧
      (∀ y ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S),
        cellSelector E choice y ≠ none) ∧
      (∀ y q, cellSelector E choice y = some q →
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n))) ∧
      ∀ (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ →
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E
            {q | LatticeProb.restrictSelector outer (cellSelector E choice) q.1 ≠
                LatticeProb.restrictSelector outer (cellSelector E choice) q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤
                ENNReal.ofReal ((m : ℝ) * ε) +
                  η := by
  have hsmall := LatticeProb.eventually_uniform_dyadic_thickening_lt_of_finite_compact_null
    P ν hν (frontier outer) isClosed_frontier hnullOuter S hη
  filter_upwards [hsmall] with n hn
  obtain ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, hcoupling⟩ :=
    exists_brownian_ball_dyadic_restricted_selector_uniform_coupling
      center radius c hS hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n
  refine ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hcoupling outer ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with k hk
  intro j v z hz
  exact (hk j v z hz).trans (add_le_add le_rfl (le_of_lt (hn j z)))

end LatticeProb.ParentBlock
