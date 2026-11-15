import LatticeProb.Prob.WalkBrownianAmbientActivityError

/-! # Uniform walk activity with a prescribed error budget -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A common horizon and endpoint-cell error budget bound the original walk's
active probability by any prescribed positive tolerance. -/
theorem walk_ambient_active_le_of_cell_error_budget
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ)
    {D : Set (Euc d)} (hD : Bornology.IsBounded D)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ (K : ℕ) (b : ℝ), 0 < b ∧ ∀ (U : J → Set (Euc d)) (_hU : ∀ j, IsOpen (U j)),
      (∀ j, U j ⊆ D) → ∀ z ∈ D, ∀ initial : J,
      ∀ (select : ℕ → Euc d → Option J) (_hs : ∀ n, Measurable (select n)),
      (∀ n x j, select n x = some j → Metric.ball x ε ⊆ U j) →
      ∀ (V : Type*) [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
        (N : FiniteConductanceNetwork V) (pos : V → Euc d) (_hinj : Function.Injective pos)
        (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
        (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
        (_hE : ∀ n i, MeasurableSet (E n i))
        (_hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
        (A : Set V) (_hBA : ∀ j, B j ⊆ A)
        (hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
        (v : V) (choice : ∀ n, Fin (m n) → Option J)
        (_hselect : ∀ n, select n = cellSelector (E n) (choice n))
        (a : ℝ)
        (_hdiam : ∀ n ≤ K, ∀ i, ∀ x ∈ E n i, ∀ y ∈ E n i, dist x y ≤ a)
        (_hinside : ∀ n < K, ∀ i j, choice n i = some j → E n i ⊆ U j)
        (_hcover : ∀ n ≤ K, ∀ j, closure (U j) ⊆ ⋃ i, E n i)
        (_herror : ∀ n < K, ∀ i j, choice n i = some j →
          ∀ w : V, pos w ∈ E n i → ∀ y ∈ E n i, ∀ l,
          |(((N.discreteHarmonicMeasure (B j) (hB j) w).map pos) (E (n + 1) l)).toReal -
            (((stoppedBrownianLaw (U j) y μ).map BouRabeeGwynne.CurveSpace.endPoint) (E (n + 1) l)).toReal| ≤
              b / (m (n + 1) + 1))
        (_hzU : z ∈ U initial)
        (_hinit : ∀ i, |(((N.discreteHarmonicMeasure (B initial) (hB initial) v).map pos)
          (E 0 i)).toReal -
          (((stoppedBrownianLaw (U initial) z μ).map BouRabeeGwynne.CurveSpace.endPoint) (E 0 i)).toReal| ≤
            b / (m 0 + 1)),
        N.trajectoryLaw A hA v
          {ω | (FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select ω K).1 = false} ≤
        ENNReal.ofReal η := by
  have hhalf : 0 < η / 2 := by positivity
  obtain ⟨K, hK⟩ := walk_ambient_active_le_brownian_tail_add_cell_error (J := J)
    hd hμ hD hε hhalf
  let b : ℝ := (η / 2) / ((K : ℝ) + 1)
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hb : 0 < b := div_pos hhalf hden
  refine ⟨K, b, hb, ?_⟩
  intro U hU hUD z hz initial select hs hmargin V _ _ _ N pos hinj B hB m E hE hdE
    A hBA hA haccess v choice hselect a hdiam hinside hcover herror hzU hinit
  refine (hK U hU hUD z hz initial select hs hmargin V N pos hinj B hB m E hE hdE
    A hBA hA haccess v choice hselect a b hb.le hdiam hinside hcover herror hzU hinit).trans ?_
  have hmul : ((K : ℝ) + 1) * b = η / 2 := by
    dsimp [b]
    exact mul_div_cancel₀ (η / 2) (ne_of_gt hden)
  have he : (K + 1 : ℝ≥0∞) * ENNReal.ofReal b = ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hmul]
  rw [he, ← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

end LatticeProb
