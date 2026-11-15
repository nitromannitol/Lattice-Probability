import LatticeProb.Prob.JointObservationLift
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Lifting the walk and Brownian excursion coupling -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- The full joint excursion law can be realized together with the original
walk trajectory, preserving both its law and the entire excursion coupling. -/
theorem exists_actualWalkBrownian_joint_lift
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) :
    ∃ ξ : Measure ((ℕ → V) × (ℕ → Bool × C(unitInterval, Euc d))),
      IsProbabilityMeasure ξ ∧ ξ.fst = N.trajectoryLaw A hA v ∧
      ξ.map (fun p => (FiniteConductanceNetwork.actualWalkExcursionSequence
        pos B initial select p.1, p.2)) =
        N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z := by
  let : Nonempty V := ⟨v⟩
  let : StandardBorelSpace (Euc d) := inferInstance
  let : StandardBorelSpace (ℕ → Euc d) := inferInstance
  let : StandardBorelSpace (ClockedWalkExcursion d) := inferInstance
  let : StandardBorelSpace (Bool × ClockedWalkExcursion d) := inferInstance
  let : StandardBorelSpace (ℕ → Bool × ClockedWalkExcursion d) := inferInstance
  let := N.walkBrownianInitialCoupling_isProbability pos B hB W hW μ m E hE hdE initial v z
  let : IsProbabilityMeasure (N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z) := by
    unfold FiniteConductanceNetwork.walkBrownianJointLaw
    infer_instance
  exact exists_joint_observation_lift (N.trajectoryLaw A hA v)
    (N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z)
    (FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select)
    (FiniteConductanceNetwork.measurable_actualWalkExcursionSequence pos B initial select)
    (N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
      hd hμ hWb hBA hA haccess initial v z).1

end LatticeProb
end
