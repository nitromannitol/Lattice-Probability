import LatticeProb.Prob.BrownianRestrictedSelectorSmallBoundary

/-! # Restricted selectors with prescribed total error -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped ENNReal Topology

namespace LatticeProb.ParentBlock

/-- A sufficiently fine dyadic scale gives any prescribed positive total
error for restricted Brownian endpoint selectors with null outer frontier. -/
theorem eventually_brownian_ball_dyadic_restricted_selector_le_budget
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
    (outer : Set (Euc 2)) (b : ℝ) (hb : 0 < b)
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
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ →
          finitePartitionCoupling (μ j k v : Measure (Euc 2))
            (ν j z : Measure (Euc 2)) E E
            {q | LatticeProb.restrictSelector outer (cellSelector E choice) q.1 ≠
                LatticeProb.restrictSelector outer (cellSelector E choice) q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤
                ENNReal.ofReal b := by
  have hhalf : 0 < b / 2 := by positivity
  have hη : 0 < ENNReal.ofReal (b / 2) := ENNReal.ofReal_pos.mpr hhalf
  filter_upwards [eventually_brownian_ball_dyadic_restricted_selector_small_boundary
    center radius c hS hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP
    outer (ENNReal.ofReal (b / 2)) hη hnullOuter] with n hn
  obtain ⟨m, E, choice, hd, hcover, hm, hbnd, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, hbound⟩ := hn
  refine ⟨m, E, choice, hd, hcover, hm, hbnd, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, ?_⟩
  have hden : 0 < (m : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδbound⟩ := hbound ((b / 2) / ((m : ℝ) + 1)) (div_pos hhalf hden)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hδbound] with k hk
  intro j v z hz
  refine (hk j v z hz).trans ?_
  have hnum : (m : ℝ) * (b / 2) ≤ (b / 2) * ((m : ℝ) + 1) := by nlinarith
  have hpart : (m : ℝ) * ((b / 2) / ((m : ℝ) + 1)) ≤ b / 2 := by
    simpa only [mul_div_assoc] using (div_le_iff₀ hden).2 hnum
  calc
    ENNReal.ofReal ((m : ℝ) * ((b / 2) / ((m : ℝ) + 1))) + ENNReal.ofReal (b / 2)
        ≤ ENNReal.ofReal (b / 2) + ENNReal.ofReal (b / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal hpart) le_rfl
    _ = ENNReal.ofReal b := by rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

end LatticeProb.ParentBlock
