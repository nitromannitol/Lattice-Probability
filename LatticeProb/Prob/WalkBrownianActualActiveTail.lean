import LatticeProb.Prob.CoupledSkeletonActiveTail
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Brownian activity under the walk coupling -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A common horizon bounds the Brownian active flag under every actual
finite-network excursion coupling with a selector of fixed positive margin. -/
theorem brownian_finiteDomain_walkCoupling_active_tail
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
        (A : Set V), (∀ j, B j ⊆ A) →
        (∀ v ∈ A, 0 < N.totalConductance v) → N.BoundaryAccessible A →
        ∀ (v : V),
        N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z
          {p | (p.2 K).1 = false} ≤ ENNReal.ofReal η := by
  obtain ⟨K, hK⟩ := brownian_finiteDomain_coupled_sequence_active_tail hd hμ U hU hUb hZ hε hη
  refine ⟨K, ?_⟩
  intro z hz initial select hs hmargin V _ _ _ N pos hinj B hB m E hE hdE A hBA hA haccess v
  apply hK z hz initial (brownianSelectorForWalk select)
    (fun n => hs (n - 1)) (fun n x j h => hmargin (n - 1) x j h)
  exact (N.walkBrownianJointLaw_marginals pos hinj B hB U hU μ select hs m E hE hdE
    hd hμ hUb hBA hA haccess initial v z).2

end LatticeProb
