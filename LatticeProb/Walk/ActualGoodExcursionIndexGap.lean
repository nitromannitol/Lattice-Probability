import LatticeProb.Euclidean.GoodExcursionIndexGap
import LatticeProb.Walk.ActualSkeletonAbsorption

/-! # Terminal indices of actual matched excursion skeletons -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace BouRabeeGwynne

/-- Good pairs of actual walk and Brownian excursions have terminal indices at
most one apart when their finite stopped stages absorb and their complete
excursions have separated endpoints. Index zero is the first excursion. -/
theorem actualSkeleton_terminal_indices_close {d : ℕ} {V J : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (U : J → Set (Euc d))
    (initial : J) (z : Euc d) (j₀ : J)
    (wselect : ℕ → V → Option J) (bselect : ℕ → Euc d → Option J)
    (ω : ℕ → V) (η : BrownianPath d)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (K N M : ℕ) (a r : ℝ) (hN : N ≤ K) (hM : M ≤ K) (hr : 2 * a < r)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K,
      ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
        brownianSkeletonExcursion U z j₀ bselect i η) ∈ goodExcursionPair pos (E i) a)
    (hwfin : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).1 ≠ ⊤)
    (hwstop : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).2.1 = true)
    (hbfin : (brownianSkeletonClock U z j₀ bselect M η).2 ≠ ∞)
    (hbstop : (brownianSkeletonExcursion U z j₀ bselect M η).1 = true)
    (hwsep : ∀ i, i + 1 < N → r ≤ dist
      (ClockedWalkExcursion.endPoint (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.2)
      (ClockedWalkExcursion.endPoint (FiniteConductanceNetwork.actualWalkStage pos B initial wselect (i + 1) ω).2.2))
    (hbsep : ∀ i, i + 1 < M → r ≤ dist
      ((brownianSkeletonExcursion U z j₀ bselect i η).2 1)
      ((brownianSkeletonExcursion U z j₀ bselect (i + 1) η).2 1)) :
    (∀ i ≤ K, (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.1 =
      (brownianSkeletonExcursion U z j₀ bselect i η).1) ∧ N ≤ M + 1 ∧ M ≤ N + 1 := by
  apply goodExcursionPair_terminal_indices_close pos m E
    (fun i => ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
      brownianSkeletonExcursion U z j₀ bselect i η)) K N M a r hN hM hr hdiam hgood
  · intro i hi
    exact FiniteConductanceNetwork.actualWalkStage_endPoint_eq_of_stopped
      pos B initial wselect ω hi hwfin hwstop
  · intro i hi
    exact brownianSkeletonExcursion_endPoint_eq_of_stopped U z j₀ bselect η hi hbfin hbstop
  · exact hwsep
  · exact hbsep

end BouRabeeGwynne
