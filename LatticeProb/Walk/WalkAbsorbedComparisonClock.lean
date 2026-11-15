import LatticeProb.Walk.ActualSkeletonAbsorption

/-! # Finite absorbed walk excursion clocks -/

set_option autoImplicit false

open scoped NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Finite walk skeleton clocks yield a monotone, zero-prepended clock which
is strict before its terminal value. The initial and active-stage strictness
assumptions are kept explicit. -/
theorem actualWalkStage_exists_absorbed_comparison_clock
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (K : ℕ) (k : ℕ → ℕ)
    (hclock : ∀ i ≤ K, (actualWalkStage pos B initial select i ω).1 = k i)
    (hzero : 0 < k 0)
    (hactive : ∀ i < K, (actualWalkStage pos B initial select (i + 1) ω).2.1 = false →
      k i < k (i + 1)) :
    ∃ T : ℕ → ℝ≥0, T 0 = 0 ∧ Monotone T ∧
      (∀ i ≤ K, T (i + 1) = k i) ∧
      (∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1)) := by
  have hkmono : ∀ i j, i ≤ j → j ≤ K → k i ≤ k j := by
    intro i j hij hj
    have h := (actualWalkStage_clock_mono pos B initial select ω) hij
    change (actualWalkStage pos B initial select i ω).1 ≤
      (actualWalkStage pos B initial select j ω).1 at h
    rw [hclock i (hij.trans hj), hclock j hj] at h
    exact WithTop.coe_le_coe.mp h
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0 (fun i => k (min i K))
  have hmono : Monotone T := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact zero_le
    | succ n =>
      change (k (min n K) : ℝ≥0) ≤ k (min (n + 1) K)
      exact_mod_cast hkmono _ _ (min_le_min_right K (Nat.le_succ n)) (min_le_right _ _)
  have hmatch : ∀ i ≤ K, T (i + 1) = k i := by
    intro i hi
    simp only [T, min_eq_left hi]
  refine ⟨T, rfl, hmono, hmatch, ?_⟩
  intro n hn hbefore
  cases n with
  | zero =>
    rw [hmatch 0 (Nat.zero_le K)]
    change (0 : ℝ≥0) < (k 0 : ℝ≥0)
    exact_mod_cast hzero
  | succ i =>
    have hi : i < K := by omega
    have hin : i + 1 ≤ K := by omega
    have hnotstop : (actualWalkStage pos B initial select (i + 1) ω).2.1 ≠ true := by
      intro hstop
      have hfin : (actualWalkStage pos B initial select (i + 1) ω).1 ≠ ⊤ := by
        rw [hclock (i + 1) hin]
        exact WithTop.coe_ne_top
      have heq := (actualWalkStage_clock_flag_eq_of_stopped pos B initial select ω hin hfin hstop).1
      rw [hclock K le_rfl, hclock (i + 1) hin] at heq
      have hk : k K = k (i + 1) := WithTop.coe_injective heq
      let τ := fun ξ => (actualWalkStage pos B initial select i ξ).1
      let choice := walkStageSelector (actualWalkStage pos B initial select i) (select i)
      have hc : choice (observedHistory τ ω) = none := by
        change (selectedClockedExcursion pos B
          (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
          (futureAt τ ω)).1 = true at hstop
        cases hc' : choice (observedHistory τ ω) with
        | none => rfl
        | some j => simp [hc', selectedClockedExcursion] at hstop
      have hsame : (actualWalkStage pos B initial select (i + 1) ω).1 =
          (actualWalkStage pos B initial select i ω).1 := by
        change nextSelectedExitTime τ B choice ω = τ ω
        simp only [nextSelectedExitTime, hc, add_zero]
      rw [hclock (i + 1) hin, hclock i (by omega)] at hsame
      have hk' : k (i + 1) = k i := WithTop.coe_injective hsame
      rw [hmatch i (by omega), hmatch K le_rfl] at hbefore
      rw [hk, hk'] at hbefore
      exact (lt_irrefl _ hbefore)
    have hflag : (actualWalkStage pos B initial select (i + 1) ω).2.1 = false := by
      cases h : (actualWalkStage pos B initial select (i + 1) ω).2.1 <;> simp_all
    rw [hmatch i (by omega), hmatch (i + 1) hin]
    exact_mod_cast hactive i hi hflag

end BouRabeeGwynne.FiniteConductanceNetwork
