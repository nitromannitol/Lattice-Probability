import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonClock
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties

/-!
# Successive exits of an unbounded continuous path

A continuous path with unbounded range leaves every bounded set after every finite time.
Consequently all successive bounded-domain exit clocks are finite.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A continuous path of unbounded range leaves each bounded set after any given time. -/
theorem exists_later_not_mem_of_unbounded_range {d : ℕ} (z : Euc d)
    (ω : BrownianPath d) (hω : ¬ Bornology.IsBounded (Set.range fun t => z + ω t))
    {U : Set (Euc d)} (hU : Bornology.IsBounded U) (T : ℝ≥0) :
    ∃ t : ℝ≥0, T ≤ t ∧ z + ω t ∉ U := by
  by_contra h
  push Not at h
  apply hω
  have hc : Bornology.IsBounded ((fun t : ℝ≥0 => z + ω t) '' Icc 0 T) :=
    (isCompact_Icc.image (continuous_const.add ω.continuous)).isBounded
  apply (hc.union hU).subset
  rintro x ⟨t, rfl⟩
  by_cases ht : t ≤ T
  · exact Or.inl ⟨t, ⟨bot_le, ht⟩, rfl⟩
  · exact Or.inr (h t (le_of_not_ge ht))

/-- Every successive exit clock is finite on a continuous path of unbounded range, for any
selector and bounded exit domains. -/
theorem brownianSkeletonClock_finite_of_unbounded_range {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, Bornology.IsBounded (U j)) (z : Euc d)
    (j₀ : J) (selector : ℕ → Euc d → Option J) (ω : BrownianPath d)
    (hω : ¬ Bornology.IsBounded (Set.range fun t => z + ω t)) (n : ℕ) :
    (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞ := by
  have hexit (j : J) (T : ℝ≥0) :
      continuousExitTime (U j) (z + ω T) (shiftedBrownianPath T ω) ≠ ∞ := by
    obtain ⟨t, ht, hout⟩ := exists_later_not_mem_of_unbounded_range z ω hω (hU j) T
    have hout' : (z + ω T) + shiftedBrownianPath T ω (t - T) ∉ U j := by
      have heq : (z + ω T) + shiftedBrownianPath T ω (t - T) = z + ω t := by
        change (z + ω T) + (ω (T + (t - T)) - ω T) = z + ω t
        rw [add_tsub_cancel_of_le ht]
        abel
      rw [heq]
      exact hout
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (continuousExitTime_le_of_not_mem hout')
  induction n with
  | zero =>
    obtain ⟨t, _, ht⟩ := exists_later_not_mem_of_unbounded_range z ω hω (hU j₀) 0
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (continuousExitTime_le_of_not_mem ht)
  | succ n ih =>
    change brownianSelectedNextExitTime U z
      (fun η => (brownianSkeletonClock U z j₀ selector n η).2)
      (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock U z j₀ selector n)) ω ≠ ∞
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none => simpa only [brownianSelectedNextExitTime, hc] using ih
    | some j =>
      simp only [brownianSelectedNextExitTime, hc, brownianNextExitTime]
      exact ENNReal.add_ne_top.mpr ⟨ih, hexit j _⟩

end BouRabeeGwynne
