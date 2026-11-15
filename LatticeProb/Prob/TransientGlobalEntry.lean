import LatticeProb.Prob.GlobalEntryHittingAfter
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage

/-! # Entry times of transient curves -/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace LatticeProb

/-- A transient curve has a finite lower bound for all visits to a bounded set.
The global entry agrees with the hitting time after that bound, even if no
visit occurs. -/
theorem exists_globalEntryClock_eq_hittingAfter_of_transient
    (c : C(ℝ, ℂ)) (V : Set ℂ)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ))
    (hV : Bornology.IsBounded V) :
    ∃ a : ℝ, globalOpenEntry (fun (_ : Unit) t => c t) V () ≠ ⊥ ∧
      entryClockOfEReal (globalOpenEntry (fun (_ : Unit) t => c t) V ()) =
        hittingAfter (fun t (_ : Unit) => c t) V a () := by
  obtain ⟨a, ha⟩ := MatedCRTHarmonic.GMS4c.exists_past_outside htr hV
  have hlower : ∀ t, c t ∈ V → a ≤ t := by
    intro t ht
    exact le_of_not_gt (fun h => ha t h ht)
  exact ⟨a, globalOpenEntry_ne_bot_of_lower_bound _ V () a hlower,
    globalEntryClock_eq_hittingAfter_of_lower_bound _ V () a hlower⟩

end LatticeProb
