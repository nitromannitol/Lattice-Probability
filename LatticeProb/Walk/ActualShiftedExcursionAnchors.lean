import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonObservation
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianGoodEvent

/-! # Anchors of actual excursion skeletons

Finite skeleton endpoints give the anchors of the zero-prepended clocks.
-/

set_option autoImplicit false

open Set
open scoped NNReal unitInterval

namespace BouRabeeGwynne

/-- Good actual excursions control the corresponding full knot anchors when
both skeleton clocks are finite and the walk path interpolates its vertices. -/
theorem actualSkeleton_shifted_anchor_bounds
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (wselect : ℕ → V → Option J) (ω : ℕ → V)
    (U : J → Set (Euc 2)) (z : Euc 2) (j₀ : J)
    (bselect : ℕ → Euc 2 → Option J) (η : BrownianPath 2)
    (F : ℝ≥0 → Euc 2) (k : ℕ → ℕ) (K : ℕ) (a : ℝ)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (hclock : ∀ i ≤ K, (FiniteConductanceNetwork.actualWalkStage
      pos B initial wselect i ω).1 = k i)
    (hinterp : ∀ i ≤ K, F (k i) = pos (ω (k i)))
    (hbfin : ∀ i ≤ K, (brownianSkeletonClock U z j₀ bselect i η).2 ≠ ⊤)
    (hstart : dist (F 0) (z + η 0) ≤ a)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K,
      ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
        brownianSkeletonExcursion U z j₀ bselect i η) ∈ goodExcursionPair pos (E i) a) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0 (fun i => k i)
    let S : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => (brownianSkeletonClock U z j₀ bselect i η).2.toNNReal)
    ∀ i ≤ K + 1, dist (F (T i)) (z + η (S i)) ≤ a := by
  dsimp only
  intro i hi
  cases i with
  | zero => exact hstart
  | succ i =>
    have hi' : i ≤ K := by omega
    have hw := FiniteConductanceNetwork.actualWalkStage_endPoint_of_clock
      pos B initial wselect i ω (k i) (hclock i hi')
    have hb := brownianSkeletonExcursion_endPoint U z j₀ bselect i η (hbfin i hi')
    change dist (F (k i)) (z + η (brownianSkeletonClock U z j₀ bselect i η).2.toNNReal) ≤ a
    have hp := goodExcursionPair_dist_le pos (E i) (hdiam i hi')
      (p := ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
        brownianSkeletonExcursion U z j₀ bselect i η)) (hgood i hi')
    change dist (ClockedWalkExcursion.endPoint
      (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.2)
      ((brownianSkeletonExcursion U z j₀ bselect i η).2 1) ≤ a at hp
    rw [hw, hb] at hp
    rw [hinterp i hi']
    exact hp

end BouRabeeGwynne
