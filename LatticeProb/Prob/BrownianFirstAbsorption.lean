import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail

/-!
# First absorption of a Brownian skeleton

A finite absorbed skeleton has a last active state at the same time as its
terminal state. This identifies the active excursion prefix before absorption.
-/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Once absorbed, every later state of the skeleton is the same. -/
theorem brownianSkeletonClock_eq_of_absorbed {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (ω : BrownianPath d)
    {m n : ℕ} (hmn : m ≤ n)
    (hstop : (brownianSkeletonClock U z j₀ selector m ω).1 = true) :
    brownianSkeletonClock U z j₀ selector n ω =
      brownianSkeletonClock U z j₀ selector m ω := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [brownianSkeletonClock_absorbed U z j₀ selector n ω (by rw [ih]; exact hstop), ih]

/-- If the flag is set by stage `K`, the first setting follows an active state;
the clock time there is unchanged through stage `K`. -/
theorem brownianSkeletonClock_exists_last_active {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (ω : BrownianPath d) (K : ℕ)
    (hstop : (brownianSkeletonClock U z j₀ selector K ω).1 = true) :
    ∃ m < K, (brownianSkeletonClock U z j₀ selector m ω).1 = false ∧
      (brownianSkeletonClock U z j₀ selector (m + 1) ω).1 = true ∧
      brownianSkeletonClock U z j₀ selector K ω =
        brownianSkeletonClock U z j₀ selector (m + 1) ω ∧
      (brownianSkeletonClock U z j₀ selector (m + 1) ω).2 =
        (brownianSkeletonClock U z j₀ selector m ω).2 := by
  classical
  have hex : ∃ n, (brownianSkeletonClock U z j₀ selector n ω).1 = true := ⟨K, hstop⟩
  have hfirst := Nat.find_spec hex
  have hbound := Nat.find_min' hex hstop
  cases hf : Nat.find hex with
  | zero => simp [hf, brownianSkeletonClock] at hfirst
  | succ m =>
    have hmstop : (brownianSkeletonClock U z j₀ selector (m + 1) ω).1 = true := by
      simpa [hf, Nat.succ_eq_add_one] using hfirst
    have hmactive : (brownianSkeletonClock U z j₀ selector m ω).1 = false := by
      have hm := Nat.find_min hex (show m < Nat.find hex by rw [hf]; omega)
      cases hh : (brownianSkeletonClock U z j₀ selector m ω).1 with
      | false => rfl
      | true => exact False.elim (hm hh)
    have hmk : m < K := by rw [hf] at hbound; omega
    have hchoice : brownianClockChoice z (selector (m + 1))
        (brownianSkeletonClock U z j₀ selector m) ω = none := by
      change (brownianClockChoice z (selector (m + 1))
        (brownianSkeletonClock U z j₀ selector m) ω).isNone = true at hmstop
      cases hc : brownianClockChoice z (selector (m + 1))
          (brownianSkeletonClock U z j₀ selector m) ω with
      | none => rfl
      | some j => simp [hc] at hmstop
    have htime : (brownianSkeletonClock U z j₀ selector (m + 1) ω).2 =
        (brownianSkeletonClock U z j₀ selector m ω).2 := by
      change brownianSelectedNextExitTime U z
        (fun η ↦ (brownianSkeletonClock U z j₀ selector m η).2)
        (brownianClockChoice z (selector (m + 1)) (brownianSkeletonClock U z j₀ selector m)) ω = _
      simp only [brownianSelectedNextExitTime, hchoice]
    exact ⟨m, hmk, hmactive, hmstop,
      brownianSkeletonClock_eq_of_absorbed U z j₀ selector ω (Nat.succ_le_of_lt hmk) hmstop,
      htime⟩

end BouRabeeGwynne
