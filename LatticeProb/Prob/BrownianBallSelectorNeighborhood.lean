import LatticeProb.Prob.BrownianBallSelectorMarginals
import LatticeProb.Prob.BrownianSelectorNeighborhoodSupport

/-! # Brownian ball selector couplings -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- A fixed dyadic selector gives couplings with exact marginals, uniformly
bounding failure to share a selected dyadic neighborhood. -/
theorem exists_brownian_ball_dyadic_selector_common_neighborhood_coupling
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
    (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))] :
    ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
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
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ →
          ∃ π : Measure (Euc 2 × Euc 2), IsProbabilityMeasure π ∧
            π.fst = (μ j k v : Measure (Euc 2)) ∧
            π.snd = (ν j z : Measure (Euc 2)) ∧
            π {q | ¬ ∃ i, cellSelector E choice q.1 = some i ∧
              cellSelector E choice q.2 = some i ∧
              q.1 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
                interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n))) ∧
              q.2 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
                interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n)))} ≤
              ENNReal.ofReal ε := by
  obtain ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, hbound⟩ :=
    exists_brownian_ball_dyadic_selector_coupling_with_marginals center radius c hS
      hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n
  refine ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := hbound ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hδbound] with k hk
  intro j v z hz
  obtain ⟨π, hprob, hfst, hsnd, herror⟩ := hk j v z hz
  refine ⟨π, hprob, hfst, hsnd, ?_⟩
  have hr : 0 < (2 * S / (2 : ℝ) ^ n) / 2 := by positivity
  have hsupport : ∀ᵐ y ∂π.snd,
      y ∈ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S := by
    rw [hsnd, hνlaw]
    exact stoppedBrownianLaw_endPoint_ae_mem_parentBlock c (le_of_lt hS)
      (hradius j) (center j) (x j z) (hcenter j) (hx j z) ρ hρ
  exact (measure_not_common_selected_neighborhood_le_of_snd_ae
    (cellSelector E choice)
    (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S)
    (fun i => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n)))
    hr hactive hmargin π hsupport).trans herror

end LatticeProb.ParentBlock
