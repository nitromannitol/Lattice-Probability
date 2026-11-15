import LatticeProb.Prob.BrownianContinuityCellComparison
import LatticeProb.Prob.PartitionDyadicChoice

/-! # Brownian continuity cells with dyadic parent choices -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- A finite family of Brownian exit laws admits common small continuity cells,
a fixed dyadic parent choice for each cell, and a uniform nearby-start mass
comparison under uniform convergence of the approximating laws. -/
theorem exists_brownian_cells_dyadic_choice_uniform_mass_comparison
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
      (stoppedBrownianLaw (U j) (x j z) ρ).map CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (ν j (p j n v) : Measure (Euc 2)) < ε)
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    {K : Set (Euc 2)} (hK : IsCompact K)
    (hKblock : K ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S)
    {b : ℝ} (hb : 0 < b) :
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
        dist (p j k v) z ≤ δ → ∀ i,
          |((μ j k v : Measure (Euc 2)) (E i)).toReal -
            ((ν j z : Measure (Euc 2)) (E i)).toReal| ≤ b := by
  classical
  have hr : 0 < (2 * S / (2 : ℝ) ^ n) / 2 := by positivity
  obtain ⟨m, E, hdisj, hcover, hmeas, hbounded, hdiam, hnull, hcompare⟩ :=
    exists_common_brownian_cells_uniform_mass_comparison (by decide) U hU hUb ρ hρ
      P x hx V p μ ν hνlaw hν hLP hK hr hb
  let : MeasurableSpace (Option (Fin m)) := ⊤
  let : MeasurableSingletonClass (Option (Fin m)) := ⟨fun _ => trivial⟩
  obtain ⟨choice, hchoice, hactive, hmargin⟩ :=
    exists_partition_dyadic_choice c hS n E K hKblock
      (fun i y hy z hz => le_of_lt (hdiam i z hz y hy)) hmeas hdisj
      (fun y hy => mem_iUnion.mp (hcover hy))
  exact ⟨m, E, choice, hdisj, hcover, hmeas, hbounded, hdiam, hnull,
    hchoice, hactive, hmargin, hcompare⟩

end LatticeProb.ParentBlock
