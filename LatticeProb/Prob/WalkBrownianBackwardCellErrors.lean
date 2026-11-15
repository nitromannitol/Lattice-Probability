import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # Backward cell estimates for finite-network and Brownian exits -/

set_option autoImplicit false

open MeasureTheory BouRabeeGwynne

namespace LatticeProb

/-- A backward diameter estimate turns comparisons on inner starting sets into
the initial and successive endpoint-cell bounds for a finite network. The
comparison itself is a hypothesis, as is containment of selected cells in the
inner starting sets. Finite stage data are extended constantly past the horizon. -/
theorem walk_brownian_cell_errors_of_backward_comparison
    {d : ℕ} {J V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (pos : V → Euc d)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (U I : J → Set (Euc d)) (μ : Measure (BrownianPath d))
    (K : ℕ) (m : Fin (K + 1) → ℕ)
    (E : ∀ i, Fin (m i) → Set (Euc d)) (δ : Fin (K + 1) → ℝ) (b : ℝ)
    (hback : ∀ i : Fin K, ∀ k, ∀ x ∈ E i.castSucc k, ∀ y ∈ E i.castSucc k,
      dist x y ≤ δ i.succ)
    (hcomp : ∀ i j (v : V), pos v ∈ I j → ∀ y ∈ I j,
      dist (pos v) y ≤ δ i → ∀ k,
        |(((N.discreteHarmonicMeasure (B j) (hB j) v).map pos) (E i k)).toReal -
          (((stoppedBrownianLaw (U j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E i k)).toReal| ≤
            b / (m i + 1))
    (choice : ∀ i, Fin (m i) → Option J)
    (hinner : ∀ i k j, choice i k = some j → E i k ⊆ I j)
    (initial : J) (v₀ : V) (z : Euc d)
    (hv₀ : pos v₀ ∈ I initial) (hz : z ∈ I initial)
    (hnear : dist (pos v₀) z ≤ δ ⟨0, Nat.zero_lt_succ K⟩) :
    let ix : ℕ → Fin (K + 1) := fun n => ⟨min n K, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m' : ℕ → ℕ := fun n => m (ix n)
    let E' : ∀ n, Fin (m' n) → Set (Euc d) := fun n => E (ix n)
    let choice' : ∀ n, Fin (m' n) → Option J := fun n => choice (ix n)
    (∀ n < K, ∀ k j, choice' n k = some j →
      ∀ v : V, pos v ∈ E' n k → ∀ y ∈ E' n k, ∀ l,
        |(((N.discreteHarmonicMeasure (B j) (hB j) v).map pos) (E' (n + 1) l)).toReal -
          (((stoppedBrownianLaw (U j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E' (n + 1) l)).toReal| ≤
            b / (m' (n + 1) + 1)) ∧
    (∀ k, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v₀).map pos)
        (E' 0 k)).toReal -
      (((stoppedBrownianLaw (U initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint) (E' 0 k)).toReal| ≤
        b / (m' 0 + 1)) := by
  dsimp only
  constructor
  · intro n hn
    have hix : (⟨min n K, Nat.lt_succ_of_le (min_le_right n K)⟩ : Fin (K + 1)) =
        (⟨n, hn⟩ : Fin K).castSucc := Fin.ext (Nat.min_eq_left hn.le)
    have hix' : (⟨min (n + 1) K, Nat.lt_succ_of_le (min_le_right (n + 1) K)⟩ : Fin (K + 1)) =
        (⟨n, hn⟩ : Fin K).succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt hn))
    rw [hix, hix']
    intro k j hkj v hv y hy l
    exact hcomp _ j v (hinner _ k j hkj hv) y (hinner _ k j hkj hy)
      (hback ⟨n, hn⟩ k (pos v) hv y hy) l
  · intro k
    exact hcomp _ initial v₀ hv₀ z hz hnear k

end LatticeProb
