import LatticeProb.Prob.NetworkBackwardCellComparison

/-! # Backward endpoint-cell errors for finite networks -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace LatticeProb

/-- Finite backward cells simultaneously control initial and successive endpoint
errors for sufficiently fine networks, assuming uniform convergence of the
endpoint laws and containment of each selected cell in its inner set. -/
theorem exists_network_backward_cells_with_errors
    {d : ℕ} (hd : 1 ≤ d) {J : Type*} [Fintype J]
    (U I : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j)) (hI : ∀ j, IsCompact (I j))
    (hIU : ∀ j, I j ⊆ U j)
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (V : ℕ → Type*) [∀ n, Fintype (V n)] [∀ n, MeasurableSpace (V n)]
    [∀ n, MeasurableSingletonClass (V n)]
    (N : ∀ n, FiniteConductanceNetwork (V n)) (pos : ∀ n, V n → Euc d)
    (hpos : ∀ n, Measurable (pos n)) (B : ∀ n, J → Set (V n))
    (hB : ∀ n j v, v ∈ B n j → 0 < (N n).totalConductance v)
    (ν : ∀ j, I j → ProbabilityMeasure (Euc d))
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) z.1 ρ).map BouRabeeGwynne.CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      ∀ hv : pos n v ∈ I j,
      levyProkhorovDist (((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n))
        (ν j ⟨pos n v, hv⟩ : Measure (Euc d)) < ε)
    (K : Set (Euc d)) (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (L : ℕ) :
    ∃ (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
      (δ : Fin (L + 1) → ℝ),
      (∀ i, 0 < δ i) ∧
      (∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l))) ∧
      (∀ i, K ⊆ ⋃ k, E i k) ∧
      (∀ i k, MeasurableSet (E i k)) ∧
      (∀ i k, Bornology.IsBounded (E i k)) ∧
      (∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a) ∧
      (∀ i : Fin L, ∀ k, ∀ x ∈ E i.castSucc k, ∀ y ∈ E i.castSucc k,
        dist x y ≤ δ i.succ) ∧
      (∀ i j k z, z ∈ I j →
        ((stoppedBrownianLaw (U j) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (frontier (E i k)) = 0) ∧
      ∀ᶠ n in atTop, ∀ (choice : ∀ i, Fin (m i) → Option J),
        (∀ i k j, choice i k = some j → E i k ⊆ I j) →
        ∀ (initial : J) (v₀ : V n) (z : Euc d),
        pos n v₀ ∈ I initial → z ∈ I initial →
        dist (pos n v₀) z ≤ δ ⟨0, Nat.zero_lt_succ L⟩ →
        let ix : ℕ → Fin (L + 1) := fun q => ⟨min q L, Nat.lt_succ_of_le (min_le_right _ _)⟩
        let m' : ℕ → ℕ := fun q => m (ix q)
        let E' : ∀ q, Fin (m' q) → Set (Euc d) := fun q => E (ix q)
        let choice' : ∀ q, Fin (m' q) → Option J := fun q => choice (ix q)
        (∀ q < L, ∀ k j, choice' q k = some j →
          ∀ v : V n, pos n v ∈ E' q k → ∀ y ∈ E' q k, ∀ l,
            |(((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n) (E' (q + 1) l)).toReal -
              (((stoppedBrownianLaw (U j) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (q + 1) l)).toReal| ≤
                b / (m' (q + 1) + 1)) ∧
        (∀ k, |(((N n).discreteHarmonicMeasure (B n initial) (hB n initial) v₀).map (pos n)
            (E' 0 k)).toReal -
          (((stoppedBrownianLaw (U initial) z ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
            b / (m' 0 + 1)) := by
  obtain ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, hcomp⟩ :=
    exists_network_backward_cells_uniform_comparison hd U I hU hUb hI hIU ρ hρ V N pos hpos B hB ν hνlaw hν hLP K hK a b ha hb L
  refine ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, ?_⟩
  filter_upwards [hcomp] with n hn
  intro choice hinner initial v₀ z hv₀ hz hnear
  exact walk_brownian_cell_errors_of_backward_comparison (N n) (pos n) (B n) (hB n)
    U I ρ L m E δ b hback hn choice hinner initial v₀ z hv₀ hz hnear

end LatticeProb
