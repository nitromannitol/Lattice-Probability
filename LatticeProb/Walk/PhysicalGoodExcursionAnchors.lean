import LatticeProb.Walk.ActualShiftedExcursionAnchors
import LatticeProb.Walk.CellConfigFiniteExit
import LatticeProb.Walk.CellConfigKnotComparison
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix

/-! # Physical anchors of paired excursion skeletons -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal ENNReal
open LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Good paired excursions bound all corresponding physical walk and Brownian
anchors up to the finite terminal stage, provided the initial anchors are close. -/
theorem physical_skeleton_anchor_bounds_of_good_excursions
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (p : H.cells → Plane) (cell : V → H.cells)
    (B : J → Set V) (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V)
    (hpos : ∀ C, 0 < H.holding C) (hunb : H.JumpTimesUnbounded (cell ∘ ω))
    {ε : ℝ≥0} (hε : 0 < ε) (K : ℕ) (k : ℕ → ℕ)
    (hclock : ∀ i ≤ K, (actualWalkStage (fun v => (ε : ℝ) • p (cell v))
      B initial select i ω).1 = k i)
    (U : J → Set (Euc 2)) (z : Euc 2) (j₀ : J)
    (selector : ℕ → Euc 2 → Option J) (β : BrownianPath 2)
    (hbFinite : (brownianSkeletonClock U z j₀ selector K β).2 ≠ ∞)
    (a : ℝ) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (hstart : dist (H.interpolatedWalk p ε (cell ∘ ω) 0) (z + β 0) ≤ a)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K,
      ((actualWalkStage (fun v => (ε : ℝ) • p (cell v)) B initial select i ω).2,
        brownianSkeletonExcursion U z j₀ selector i β) ∈
          goodExcursionPair (fun v => (ε : ℝ) • p (cell v)) (E i) a) :
    let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => scaledJumpTime H (cell ∘ ω) hpos ε (k (min i K)))
    let Q : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
      (fun i => (brownianSkeletonClock U z j₀ selector (min i K) β).2.toNNReal)
    ∀ n ≤ K + 1, dist
      (Complex.orthonormalBasisOneI.repr.symm (H.interpolatedWalk p ε (cell ∘ ω) (T n)))
      (Complex.orthonormalBasisOneI.repr.symm (z + β (Q n))) ≤ a := by
  dsimp only
  intro n hn
  rw [Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq]
  cases n with
  | zero => exact hstart
  | succ i =>
    have hi : i ≤ K := by omega
    simp only [min_eq_left hi]
    have hw := actualWalkStage_endPoint_of_clock
      (fun v => (ε : ℝ) • p (cell v)) B initial select i ω (k i) (hclock i hi)
    have hb := brownianSkeletonExcursion_endPoint U z j₀ selector i β
      (brownianSkeletonClock_finite_of_le U z j₀ selector β hi hbFinite)
    have hp := goodExcursionPair_dist_le (fun v => (ε : ℝ) • p (cell v)) (E i)
      (hdiam i hi) (hgood i hi)
    change dist (ClockedWalkExcursion.endPoint
      (actualWalkStage (fun v => (ε : ℝ) • p (cell v)) B initial select i ω).2.2)
      ((brownianSkeletonExcursion U z j₀ selector i β).2 1) ≤ a at hp
    rw [hw, hb] at hp
    have hknot := interpolatedWalk_at_jumpTime H p (cell ∘ ω) hpos hunb (k i) hε
    change H.interpolatedWalk p ε (cell ∘ ω)
      (scaledJumpTime H (cell ∘ ω) hpos ε (k i)) = _ at hknot
    rw [hknot]
    exact hp

end BouRabeeGwynne.FiniteConductanceNetwork
end
