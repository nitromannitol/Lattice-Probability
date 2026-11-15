import LatticeProb.Walk.ActualSkeletonAbsorption
import LatticeProb.Walk.CellConfigKnotComparison

/-! # Advancing clocks of selected walk stages -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal
open LatticeProb.CellConfigInterpolation

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- A strict advance of a selected walk clock implies that the successor
stage is active. -/
theorem actualWalkStage_active_of_clock_lt
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (n : ℕ)
    (hadvance : (actualWalkStage pos B initial select n ω).1 <
      (actualWalkStage pos B initial select (n + 1) ω).1) :
    (actualWalkStage pos B initial select (n + 1) ω).2.1 = false := by
  have hnotstop : (actualWalkStage pos B initial select (n + 1) ω).2.1 ≠ true := by
    intro hstop
    let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
    let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
    have hc : choice (observedHistory τ ω) = none := by
      change (selectedClockedExcursion pos B
        (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
        (futureAt τ ω)).1 = true at hstop
      cases hc' : choice (observedHistory τ ω) with
      | none => rfl
      | some j => simp [hc', selectedClockedExcursion] at hstop
    have hsame : (actualWalkStage pos B initial select (n + 1) ω).1 =
        (actualWalkStage pos B initial select n ω).1 := by
      change nextSelectedExitTime τ B choice ω = τ ω
      simp only [nextSelectedExitTime, hc, add_zero]
    exact (ne_of_lt hadvance) hsame.symm
  cases h : (actualWalkStage pos B initial select (n + 1) ω).2.1 <;> simp_all


/-- A strict physical jump-clock advance forces the next selected stage to
be active. -/
theorem actualWalkStage_active_of_physical_clock_lt
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (cell : V → H.cells) (pos : V → Euc 2) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V) (n k l : ℕ)
    (hpos : ∀ C, 0 < H.holding C) {ε : ℝ≥0} (hε : 0 < ε)
    (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l)
    (hadvance : scaledJumpTime H (cell ∘ ω) hpos ε k <
      scaledJumpTime H (cell ∘ ω) hpos ε l) :
    (actualWalkStage pos B initial select (n + 1) ω).2.1 = false := by
  have hq : StrictMono (scaledJumpTime H (cell ∘ ω) hpos ε) := by
    intro a b hab
    apply NNReal.coe_lt_coe.mp
    exact mul_lt_mul_of_pos_left (H.jumpTime_strictMono hpos hab)
      (sq_pos_of_pos (by exact_mod_cast hε))
  apply actualWalkStage_active_of_clock_lt pos B initial select ω n
  rw [hk, hl]
  exact WithTop.coe_lt_coe.mpr (hq.lt_iff_lt.mp hadvance)

end BouRabeeGwynne.FiniteConductanceNetwork
end
