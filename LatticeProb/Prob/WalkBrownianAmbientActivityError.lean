import LatticeProb.Prob.WalkBrownianAmbientActiveTail
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # Uniform walk activity bounds from endpoint estimates -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A common horizon bounds the original walk's active probability by a
Brownian tail and explicit endpoint-cell error estimates. -/
theorem walk_ambient_active_le_brownian_tail_add_cell_error
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ)
    {D : Set (Euc d)} (hD : Bornology.IsBounded D)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (U : J → Set (Euc d)) (_hU : ∀ j, IsOpen (U j)),
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
        (a b : ℝ) (_hb : 0 ≤ b)
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
        ENNReal.ofReal η + (K + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨K, hK⟩ := walk_ambient_active_le_brownian_tail_add_failure (J := J)
    hd hμ hD hε hη
  refine ⟨K, ?_⟩
  intro U hU hUD z hz initial select hs hmargin V _ _ _ N pos hinj B hB m E hE hdE
    A hBA hA haccess v choice hselect a b hb hdiam hinside hcover herror hzU hinit
  exact (hK U hU hUD z hz initial select hs hmargin V N pos hinj B hB m E hE hdE
    A hBA hA haccess v a).trans (add_le_add le_rfl
      (N.walkBrownianJointLaw_firstFailure_le hd pos hinj B hB U hU
        (fun j => hD.subset (hUD j)) μ hμ select hs m E hE hdE choice hselect K
        hb hdiam hinside hcover herror initial v z hzU hinit))

end LatticeProb
