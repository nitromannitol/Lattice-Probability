import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianActiveTransfer
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail

/-! # Uniform walk activity bounds in bounded ambient sets -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped ENNReal

namespace LatticeProb

/-- A common horizon bounds the original walk's active probability by a
Brownian tail and the first-failure probability of the excursion coupling. -/
theorem walk_ambient_active_le_brownian_tail_add_failure
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ)
    {D : Set (Euc d)} (hD : Bornology.IsBounded D)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)),
      (∀ j, U j ⊆ D) → ∀ z ∈ D, ∀ initial : J,
      ∀ (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n)),
      (∀ n x j, select n x = some j → Metric.ball x ε ⊆ U j) →
      ∀ (V : Type*) [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
        (N : FiniteConductanceNetwork V) (pos : V → Euc d) (hinj : Function.Injective pos)
        (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
        (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
        (hE : ∀ n i, MeasurableSet (E n i))
        (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
        (A : Set V) (_hBA : ∀ j, B j ⊆ A)
        (hA : ∀ v ∈ A, 0 < N.totalConductance v) (_haccess : N.BoundaryAccessible A)
        (v : V) (a : ℝ),
        N.trajectoryLaw A hA v
          {ω | (FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select ω K).1 = false} ≤
        ENNReal.ofReal η +
          N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z
            {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} := by
  obtain ⟨K, hK⟩ := standardBrownianLaw_uniform_activeSkeletonTail (J := J)
    hd hμ hD hε hη
  refine ⟨K, ?_⟩
  intro U hU hUD z hz initial select hs hmargin V _ _ _ N pos hinj B hB m E hE hdE
    A hBA hA haccess v a
  have htail := hK U hU hUD z hz initial (brownianSelectorForWalk select)
    (fun n => hs (n - 1)) (fun n x j h => hmargin (n - 1) x j h)
  have htail' : μ {ω | (brownianSkeletonExcursion U z initial
      (brownianSelectorForWalk select) K ω).1 = false} ≤ ENNReal.ofReal η := by
    simpa only [brownianSkeletonExcursion_flag] using htail
  exact (N.trajectoryLaw_walkActive_le_brownianActive_add_failure hd pos hinj B hB U hU
    (fun j => hD.subset (hUD j)) μ hμ select hs m E hE hdE hBA hA haccess initial v z a K).trans
    (add_le_add htail' le_rfl)

end LatticeProb
