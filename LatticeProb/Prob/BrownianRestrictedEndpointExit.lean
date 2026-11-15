import LatticeProb.Prob.BrownianRestrictedSelectorMarginals
import LatticeProb.Prob.RestrictedSelectorExitEvent

/-! # Restricted endpoint exit estimates -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped ENNReal Topology

namespace LatticeProb.ParentBlock

/-- At sufficiently fine scales, endpoint probabilities outside a covered set
are uniformly close under the prescribed error. -/
theorem eventually_brownian_ball_dyadic_restricted_endpoint_exit_bounds
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
          (μ j k v : Measure (Euc 2)) outerᶜ ≤
              (ν j z : Measure (Euc 2)) outerᶜ + ENNReal.ofReal b ∧
            (ν j z : Measure (Euc 2)) outerᶜ ≤
              (μ j k v : Measure (Euc 2)) outerᶜ + ENNReal.ofReal b := by
  filter_upwards [eventually_brownian_ball_dyadic_restricted_selector_coupling_with_marginals
    center radius c hS hcenter hradius ρ hρ P x hx V p μ ν hνlaw hν hLP
    outer b hb hnullOuter] with n hn
  obtain ⟨m, E, choice, hd, hcover, hm, hbnd, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, δ, hδ, hbound⟩ := hn
  refine ⟨m, E, choice, hd, hcover, hm, hbnd, hdiam, hnull, hfiber,
    hmeas, hactive, hmargin, δ, hδ, ?_⟩
  filter_upwards [hbound] with k hk
  intro j v z hz
  obtain ⟨π, hπ, hfst, hsnd, herr⟩ := hk j v z hz
  have hact : ∀ y ∈ outer, cellSelector E choice y ≠ none :=
    fun y hy => hactive y (hcovered hy)
  have hevent := LatticeProb.restrictedSelector_exit_event_le_of_coupling π
    outer outer houter houter (cellSelector E choice) (cellSelector E choice) hact hact
  rw [hfst, hsnd] at hevent
  have hbad : π {q | LatticeProb.restrictSelector outer (cellSelector E choice) q.1 ≠
      LatticeProb.restrictSelector outer (cellSelector E choice) q.2} ≤ ENNReal.ofReal b :=
    (measure_mono (fun _ h => Or.inl h)).trans herr
  exact ⟨hevent.1.trans (add_le_add_right hbad _), hevent.2.trans (add_le_add_right hbad _)⟩

end LatticeProb.ParentBlock
