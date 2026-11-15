import LatticeProb.Prob.BrownianDyadicCellCoupling
import LatticeProb.Euclidean.ParentBlockExitGeometry

/-! # Dyadic coupling for Brownian exits from balls -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- Ball frontier support yields common dyadic cells and uniform coupling bounds. -/
theorem exists_brownian_ball_dyadic_cells_uniform_coupling
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
      y ∈ frontier (ball (center j) (radius j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S) ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < (2 * S / (2 : ℝ) ^ n) / 2) ∧
      (∀ j i z, (ν j z : Measure (Euc 2)) (frontier (E i)) = 0) ∧
      Measurable (cellSelector E choice) ∧
      (∀ y ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S),
        cellSelector E choice y ≠ none) ∧
      (∀ y q, cellSelector E choice y = some q →
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ → ∀ B : Set (Euc 2 × Euc 2),
          (∀ i, Disjoint B (E i ×ˢ E i)) →
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E B ≤ ENNReal.ofReal ((m : ℝ) * ε) := by
  apply exists_brownian_dyadic_cells_uniform_coupling
    (fun j => ball (center j) (radius j)) (fun _ => isOpen_ball)
    (fun _ => isBounded_ball) ρ hρ P x hx V p μ ν hνlaw hν hLP c hS n
    (isCompact_parentBlock_preimage c hS.le) (Subset.refl _) ?_ hε
  intro j z
  exact (hsupport j z).mono fun y hy =>
    frontier_ball_subset_parentBlock_preimage hS.le (hradius j) (hcenter j) hy

end LatticeProb.ParentBlock
