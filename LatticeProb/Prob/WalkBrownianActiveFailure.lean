import LatticeProb.Prob.WalkBrownianActualActiveTail
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! # Brownian activity and coupling failures -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A uniform horizon controls both Brownian activity and the first failure
of the finite-network walk and Brownian excursion coupling. -/
theorem brownian_finiteDomain_walkCoupling_active_or_firstFailure
    {d : ℕ} {J : Type*} [Fintype J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j))
    (hUb : ∀ j, Bornology.IsBounded (U j))
    {Z : Set (Euc d)} (hZ : Bornology.IsBounded Z)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ z ∈ Z, ∀ initial : J,
      ∀ (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)),
      (∀ n x j, select n x = some j → Metric.ball x ε ⊆ U j) →
      ∀ (V : Type*) [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
        (N : FiniteConductanceNetwork V) (pos : V → Euc d) (hinj : Function.Injective pos)
        (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
        (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
        (hE : ∀ n i, MeasurableSet (E n i))
        (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
        (A : Set V) (_hBA : ∀ j, B j ⊆ A)
        (_hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
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
        N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z
          ({p | (p.2 K).1 = false} ∪
            {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a}) ≤
          ENNReal.ofReal η + (K + 1 : ℝ≥0∞) * ENNReal.ofReal b := by
  obtain ⟨K, hK⟩ := brownian_finiteDomain_walkCoupling_active_tail hd hμ U hU hUb hZ hε hη
  refine ⟨K, ?_⟩
  intro z hz initial select hs hmargin V _ _ _ N pos hinj B hB m E hE hdE A hBA hA haccess
    v choice hselect a b hb hdiam hinside hcover herror hzU hinit
  exact (measure_union_le _ _).trans (add_le_add
    (hK z hz initial select hs hmargin V N pos hinj B hB m E hE hdE A hBA hA haccess v)
    (N.walkBrownianJointLaw_firstFailure_le hd pos hinj B hB U hU hUb μ hμ select hs m E hE hdE
      choice hselect K hb hdiam hinside hcover herror initial v z hzU hinit))

end LatticeProb
