import LatticeProb.Prob.BrownianBallDyadicCoupling

/-! # Dyadic selector coupling for Brownian exits from balls -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped Topology

namespace LatticeProb.ParentBlock

/-- The common dyadic selector agrees on coupled endpoints up to a controlled
error; the same error also bounds separation by the cell diameter. -/
theorem exists_brownian_ball_dyadic_selector_coupling
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
        dist (p j k v) z ≤ δ →
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E
            {q | cellSelector E choice q.1 ≠ cellSelector E choice q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤
                ENNReal.ofReal ((m : ℝ) * ε) := by
  obtain ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hmeas, hactive,
    hmargin, δ, hδ, hbound⟩ :=
    exists_brownian_ball_dyadic_cells_uniform_coupling center radius c hS hcenter
      hradius ρ hρ P x hx V p μ ν hνlaw hν hLP n hsupport hε
  refine ⟨m, E, choice, hd, hcover, hm, hb, hdiam, hnull, hmeas, hactive,
    hmargin, δ, hδ, ?_⟩
  filter_upwards [hbound] with k hk
  intro j v z hz
  apply hk j v z hz
  intro i
  apply Set.disjoint_left.mpr
  intro q hbad hq
  have hx' := (cellLabel_eq_some_iff E hd q.1 i).mpr hq.1
  have hy' := (cellLabel_eq_some_iff E hd q.2 i).mpr hq.2
  rcases hbad with hne | hfar
  · exact hne ((cellSelector_of_label E choice hx').trans
      (cellSelector_of_label E choice hy').symm)
  · exact (not_le_of_gt (hdiam i q.1 hq.1 q.2 hq.2)) hfar

end LatticeProb.ParentBlock
