import LatticeProb.Prob.BackwardBrownianCellComparison
import LatticeProb.Prob.WalkBrownianBackwardCellErrors

/-! # Backward endpoint comparisons for finite networks -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace LatticeProb

/-- The embedded endpoint law of a finite-network walk. -/
noncomputable def networkEndpointProbability
    {d : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (pos : V → Euc d) (hpos : Measurable pos)
    (B : Set V) (hB : ∀ v, v ∈ B → 0 < N.totalConductance v) (v : V) :
    ProbabilityMeasure (Euc d) :=
  ⟨(N.discreteHarmonicMeasure B hB v).map pos,
    (Measure.isProbabilityMeasure_map_iff hpos.aemeasurable).2 inferInstance⟩

/-- Backward cells for finite networks, with physical nearby-start comparisons
on compact inner sets. Continuity and uniform convergence of endpoint laws are
assumptions. -/
theorem exists_network_backward_cells_uniform_comparison
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
      ∀ᶠ n in atTop, ∀ i j (v : V n), pos n v ∈ I j → ∀ y ∈ I j,
        dist (pos n v) y ≤ δ i → ∀ k,
          |(((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n) (E i k)).toReal -
            (((stoppedBrownianLaw (U j) y ρ).map BouRabeeGwynne.CurveSpace.endPoint) (E i k)).toReal| ≤
              b / (m i + 1) := by
  classical
  let P : J → Type _ := fun j => I j
  let W : ∀ j, ℕ → Type _ := fun j n => {v : V n // pos n v ∈ I j}
  let p : ∀ j n, W j n → P j := fun _ _ v => ⟨pos _ v.1, v.2⟩
  let Q : ∀ j n, W j n → ProbabilityMeasure (Euc d) := fun j n v =>
    networkEndpointProbability (N n) (pos n) (hpos n) (B n j) (hB n j) v.1
  have : ∀ j, CompactSpace (P j) := fun j => isCompact_iff_compactSpace.mp (hI j)
  have hQ : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : W j n,
      levyProkhorovDist (Q j n v : Measure (Euc d)) (ν j (p j n v) : Measure (Euc d)) < ε := by
    intro j ε hε
    filter_upwards [hLP j ε hε] with n hn v
    exact hn v.1 v.2
  obtain ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, hnull, hcomp⟩ :=
    exists_backward_brownian_cells_uniform_mass_comparison P W p Q ν K a b hd U hU hUb ρ hρ
      (fun _ z => z.1) (fun j z => hIU j z.2) hνlaw hν hQ hK ha hb L
  refine ⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, hdiam, hback, ?_, ?_⟩
  · intro i j k z hz
    rw [← hνlaw j ⟨z, hz⟩]
    exact hnull i j k ⟨z, hz⟩
  · filter_upwards [hcomp] with n hn i j v hv y hy hdist k
    have h := hn i j ⟨v, hv⟩ ⟨y, hy⟩ hdist k
    change |(((N n).discreteHarmonicMeasure (B n j) (hB n j) v).map (pos n) (E i k)).toReal -
      ((ν j ⟨y, hy⟩ : Measure (Euc d)) (E i k)).toReal| ≤ b / (m i + 1) at h
    rw [hνlaw] at h
    exact h

end LatticeProb
