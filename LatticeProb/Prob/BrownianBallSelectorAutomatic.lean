import LatticeProb.Prob.BrownianBallSelectorUniform
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicNearClosureBrownianExit

/-! # Uniform Brownian ball selectors with endpoint support -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- The stopped Brownian endpoint law supplies frontier support for a fixed dyadic
selector, uniformly for nearby starts and every positive error tolerance. -/
theorem exists_brownian_ball_dyadic_selector_uniform_coupling_of_law
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
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E
            {q | cellSelector E choice q.1 ≠ cellSelector E choice q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤
                ENNReal.ofReal ((m : ℝ) * ε) := by
  apply exists_brownian_ball_dyadic_selector_uniform_coupling center radius c hS
    hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n
  intro j z
  rw [hνlaw j z]
  exact standardBrownianLaw_stopped_endPoint_ae_mem_frontier (by norm_num) hρ
    isOpen_ball isBounded_ball (hx j z)

end LatticeProb.ParentBlock
