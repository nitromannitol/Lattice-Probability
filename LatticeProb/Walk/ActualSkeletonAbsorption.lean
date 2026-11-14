import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonObservation
import LatticeProb.Prob.BrownianFirstAbsorption
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion

/-! # Absorption of excursion skeleton endpoints -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Preorder
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- A stopped finite stage has the same clock and flag at every later stage. -/
theorem actualWalkStage_clock_flag_eq_of_stopped
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) {m n : ℕ} (hmn : m ≤ n)
    (hfin : (actualWalkStage pos B initial select m ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select m ω).2.1 = true) :
    (actualWalkStage pos B initial select n ω).1 =
      (actualWalkStage pos B initial select m ω).1 ∧
    (actualWalkStage pos B initial select n ω).2.1 = true := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, hstop⟩
  | succ n hmn ih =>
    have hfn : (actualWalkStage pos B initial select n ω).1 ≠ ⊤ := by
      rw [ih.1]
      exact hfin
    let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
    let h := observedHistory τ ω
    have hflag : (actualWalkStage pos B initial select n h.2).2.1 = true := by
      rw [actualWalkStage_observedPast pos B initial select n ω hfn]
      exact ih.2
    have hchoice : walkStageSelector (actualWalkStage pos B initial select n)
        (select n) h = none := by
      simp only [walkStageSelector, hflag, ↓reduceIte]
    have hclock : (actualWalkStage pos B initial select (n + 1) ω).1 =
        (actualWalkStage pos B initial select n ω).1 := by
      change nextSelectedExitTime τ B
        (walkStageSelector (actualWalkStage pos B initial select n) (select n)) ω = τ ω
      unfold nextSelectedExitTime
      change walkStageSelector (actualWalkStage pos B initial select n)
        (select n) (observedHistory τ ω) = none at hchoice
      rw [hchoice]
      exact add_zero _
    exact ⟨hclock.trans ih.1,
      actualWalkStage_stopped_permanent pos B initial select n ω hfn ih.2⟩

/-- Endpoint positions remain fixed after a finite stopped walk stage. -/
theorem actualWalkStage_endPoint_eq_of_stopped
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) {m n : ℕ} (hmn : m ≤ n)
    (hfin : (actualWalkStage pos B initial select m ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select m ω).2.1 = true) :
    ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select n ω).2.2 =
      ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select m ω).2.2 := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have heq := (actualWalkStage_clock_flag_eq_of_stopped pos B initial select ω hmn hfin hstop).1
  rw [actualWalkStage_endPoint_of_clock pos B initial select n ω k (heq.trans hk.symm),
    actualWalkStage_endPoint_of_clock pos B initial select m ω k hk.symm]

end BouRabeeGwynne.FiniteConductanceNetwork

namespace BouRabeeGwynne

/-- Endpoint positions remain fixed after a finite stopped Brownian stage. -/
theorem brownianSkeletonExcursion_endPoint_eq_of_stopped {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (ω : BrownianPath d) {m n : ℕ} (hmn : m ≤ n)
    (hfin : (brownianSkeletonClock U z j₀ selector m ω).2 ≠ ∞)
    (hstop : (brownianSkeletonExcursion U z j₀ selector m ω).1 = true) :
    (brownianSkeletonExcursion U z j₀ selector n ω).2 1 =
      (brownianSkeletonExcursion U z j₀ selector m ω).2 1 := by
  rw [brownianSkeletonExcursion_flag] at hstop
  have heq := brownianSkeletonClock_eq_of_absorbed U z j₀ selector ω hmn hstop
  have hfn : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞ := by
    rw [heq]
    exact hfin
  rw [brownianSkeletonExcursion_endPoint U z j₀ selector n ω hfn,
    brownianSkeletonExcursion_endPoint U z j₀ selector m ω hfin, heq]

end BouRabeeGwynne
