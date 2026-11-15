import LatticeProb.Prob.BrownianCellsDyadicChoice
import LatticeProb.Prob.UniformCellCoupling

/-! # Brownian continuity cells and uniform finite-partition couplings -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- A compact set carrying the reference laws yields common continuity cells,
dyadic parent choices, and a uniform bound for their partition coupling. -/
theorem exists_brownian_dyadic_cells_uniform_coupling
    {J : Type*} [Fintype J]
    (U : J → Set (Euc 2)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (x : ∀ j, P j → Euc 2) (hx : ∀ j z, x j z ∈ U j)
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc 2))
    (ν : ∀ j, P j → ProbabilityMeasure (Euc 2))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc 2)) =
      (stoppedBrownianLaw (U j) (x j z) ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (ν j (p j n v) : Measure (Euc 2)) < ε)
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    {K : Set (Euc 2)} (hK : IsCompact K)
    (hKblock : K ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S)
    (hsupport : ∀ j z, ∀ᵐ y ∂(ν j z : Measure (Euc 2)), y ∈ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧ K ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < (2 * S / (2 : ℝ) ^ n) / 2) ∧
      (∀ j i z, (ν j z : Measure (Euc 2)) (frontier (E i)) = 0) ∧
      Measurable (cellSelector E choice) ∧
      (∀ y ∈ K, cellSelector E choice y ≠ none) ∧
      (∀ y q, cellSelector E choice y = some q →
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ → ∀ B : Set (Euc 2 × Euc 2),
          (∀ i, Disjoint B (E i ×ˢ E i)) →
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E B ≤ ENNReal.ofReal ((m : ℝ) * ε) := by
  classical
  obtain ⟨m, E, choice, hdisj, hcover, hmeas, hbounded, hdiam, hnull,
    hchoice, hactive, hmargin, _⟩ :=
    exists_brownian_cells_dyadic_choice_uniform_mass_comparison U hU hUb ρ hρ
      P x hx V p μ ν hνlaw hν hLP c hS n hK hKblock hε
  have hfull : ∀ j z, (ν j z : Measure (Euc 2)) (⋃ i, E i) = 1 := by
    intro j z
    have hae : ∀ᵐ y ∂(ν j z : Measure (Euc 2)), y ∈ ⋃ i, E i :=
      (hsupport j z).mono fun _ hy => hcover hy
    have hm : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion hmeas
    simpa only [measure_univ] using (ae_mem_iff_measure_eq hm.nullMeasurableSet).mp hae
  obtain ⟨δ, hδ, hbound⟩ := finite_uniform_nearby_partition_coupling_bad_le
    P V p μ ν hν hLP E hmeas hdisj hnull hfull hε
  exact ⟨m, E, choice, hdisj, hcover, hmeas, hbounded, hdiam, hnull,
    hchoice, hactive, hmargin, δ, hδ, by simpa using hbound⟩

end LatticeProb.ParentBlock
