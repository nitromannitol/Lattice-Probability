import LatticeProb.Prob.BrownianBallSelectorContinuity
import LatticeProb.Prob.CellSelectorCoupling

/-! # A fixed selector for uniformly coupled Brownian ball exits -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- One dyadic selector and its continuity partition work for every positive
error tolerance, with a tolerance-dependent modulus for nearby starts. -/
theorem exists_brownian_ball_dyadic_selector_uniform_coupling
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
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    (hsupport : ∀ j z, ∀ᵐ y ∂(ν j z : Measure (Euc 2)),
      y ∈ frontier (ball (center j) (radius j))) :
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
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E
            {q | cellSelector E choice q.1 ≠ cellSelector E choice q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤
                ENNReal.ofReal ((m : ℝ) * ε) := by
  obtain ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, _⟩ :=
    exists_brownian_ball_dyadic_selector_continuity_coupling center radius c hS
      hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n hsupport (by norm_num : (0 : ℝ) < 1)
  have hfull : ∀ j z, (ν j z : Measure (Euc 2)) (⋃ i, E i) = 1 := by
    intro j z
    have hae : ∀ᵐ y ∂(ν j z : Measure (Euc 2)), y ∈ ⋃ i, E i :=
      (hsupport j z).mono fun y hy => hcover
        (frontier_ball_subset_parentBlock_preimage hS.le (hradius j) (hcenter j) hy)
    have hmeasUnion : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion hm
    simpa only [measure_univ] using (ae_mem_iff_measure_eq hmeasUnion.nullMeasurableSet).mp hae
  refine ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, ?_⟩
  intro ε hε
  simpa only [Fintype.card_fin] using
    (LatticeProb.finite_uniform_nearby_partition_coupling_selector_error_le
      P V p μ ν hν hLP E choice hm hd hnull hfull
      ((2 * S / (2 : ℝ) ^ n) / 2) hdiam hε)

end LatticeProb.ParentBlock
