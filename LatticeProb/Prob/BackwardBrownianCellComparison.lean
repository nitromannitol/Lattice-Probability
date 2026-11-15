import LatticeProb.Prob.BrownianContinuityCellComparison

/-! # Backward continuity-cell comparisons for finitely many stages

The backward stage construction follows Leonardo Bonanno's
`BouRabeeGwynne.BackwardExitPartitions` in lean-formalizations, commit fdb5cad.
-/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace LatticeProb

section
variable {d : ℕ} {J : Type*} [Fintype J]
variable (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
variable (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
variable (μ : ∀ j n, V j n → ProbabilityMeasure (Euc d))
variable (ν : ∀ j, P j → ProbabilityMeasure (Euc d))
variable (K : Set (Euc d)) (a b : ℝ)

private structure ComparisonStage where
  card : ℕ
  cell : Fin card → Set (Euc d)
  modulus : ℝ
  modulus_pos : 0 < modulus
  disjoint : Pairwise (fun i j => Disjoint (cell i) (cell j))
  cover : K ⊆ ⋃ i, cell i
  measurable : ∀ i, MeasurableSet (cell i)
  bounded : ∀ i, Bornology.IsBounded (cell i)
  diameter : ∀ i, ∀ x ∈ cell i, ∀ y ∈ cell i, dist x y ≤ a
  frontier_null : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (cell i)) = 0
  comparison : ∀ᶠ n in atTop, ∀ j (v : V j n) (z : P j),
    dist (p j n v) z ≤ modulus → ∀ i,
      |((μ j n v : Measure (Euc d)) (cell i)).toReal -
        ((ν j z : Measure (Euc d)) (cell i)).toReal| ≤ b / (card + 1)

/-- Common continuity cells may be chosen backwards over a finite stage horizon.
The comparison is uniform in the domain and the approximating start, assuming
uniform convergence of the approximating endpoint laws. -/
theorem exists_backward_brownian_cells_uniform_mass_comparison
    (hd : 1 ≤ d) (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    (ρ : Measure (BrownianPath d)) (hρ : IsStandardBrownianLaw ρ)
    (x : ∀ j, P j → Euc d) (hx : ∀ j z, x j z ∈ U j)
    (hνlaw : ∀ j z, (ν j z : Measure (Euc d)) =
      (stoppedBrownianLaw (U j) (x j z) ρ).map CurveSpace.endPoint)
    (hν : ∀ j, Continuous (ν j))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc d))
        (ν j (p j n v) : Measure (Euc d)) < ε)
    (hK : IsCompact K) (ha : 0 < a) (hb : 0 < b) (L : ℕ) :
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
      (∀ i j k z, (ν j z : Measure (Euc d)) (frontier (E i k)) = 0) ∧
      ∀ᶠ n in atTop, ∀ i j (v : V j n) (z : P j),
        dist (p j n v) z ≤ δ i → ∀ k,
          |((μ j n v : Measure (Euc d)) (E i k)).toReal -
            ((ν j z : Measure (Euc d)) (E i k)).toReal| ≤ b / (m i + 1) := by
  classical
  let S := ComparisonStage P V p μ ν K a b
  have hstage (η : ℝ) (hη : 0 < η) :
      ∃ Q : S, ∀ k, ∀ x ∈ Q.cell k, ∀ y ∈ Q.cell k, dist x y ≤ η := by
    obtain ⟨m, E, hdisj, hcover, hmeas, hbounded, hdiam, hnull⟩ :=
      exists_common_brownian_exit_continuity_cells hd hρ U hU hUb hK (lt_min ha hη)
    have hn : ∀ j i z, (ν j z : Measure (Euc d)) (frontier (E i)) = 0 := by
      intro j i z
      rw [hνlaw]
      exact hnull j (x j z) (hx j z) i
    obtain ⟨δ, hδ, hcomp⟩ := finite_uniform_nearby_cell_mass_error P V p μ ν hν hLP E hn
      (show 0 < b / (m + 1) by positivity)
    refine ⟨⟨m, E, δ, hδ, hdisj, hcover, hmeas, hbounded, ?_, hn, hcomp⟩, ?_⟩
    · intro i y hy z hz
      exact (hdiam i y hy z hz).le.trans (min_le_left _ _)
    · intro i y hy z hz
      exact (hdiam i y hy z hz).le.trans (min_le_right _ _)
  let start : S := (hstage 1 zero_lt_one).choose
  let next : S → S := fun Q => (hstage Q.modulus Q.modulus_pos).choose
  have hnext (Q : S) : ∀ k, ∀ x ∈ (next Q).cell k, ∀ y ∈ (next Q).cell k,
      dist x y ≤ Q.modulus := (hstage Q.modulus Q.modulus_pos).choose_spec
  let seq : ℕ → S := Nat.rec start (fun _ Q => next Q)
  let Q : Fin (L + 1) → S := fun i => seq (L - i.val)
  have hback (i : Fin L) : ∀ k, ∀ x ∈ (Q i.castSucc).cell k,
      ∀ y ∈ (Q i.castSucc).cell k, dist x y ≤ (Q i.succ).modulus := by
    change ∀ k, ∀ x ∈ (seq (L - i.val)).cell k,
      ∀ y ∈ (seq (L - i.val)).cell k, dist x y ≤ (seq (L - (i.val + 1))).modulus
    have hidx : L - i.val = (L - (i.val + 1)) + 1 := by omega
    rw [hidx]
    exact hnext (seq (L - (i.val + 1)))
  refine ⟨fun i => (Q i).card, fun i => (Q i).cell, fun i => (Q i).modulus,
    fun i => (Q i).modulus_pos, fun i => (Q i).disjoint, fun i => (Q i).cover,
    fun i => (Q i).measurable, fun i => (Q i).bounded, fun i => (Q i).diameter,
    hback, fun i => (Q i).frontier_null, ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => (Q i).comparison)] with n hn
  exact hn

end
end LatticeProb
