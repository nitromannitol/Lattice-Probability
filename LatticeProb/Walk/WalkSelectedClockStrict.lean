import LatticeProb.Walk.WalkAbsorbedComparisonClock

/-! # Strictness of selected walk excursion clocks -/

set_option autoImplicit false

open Preorder
open scoped NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- A discrete walk starting in a set cannot exit it at time zero. -/
theorem exitTime_pos_of_mem {V : Type*} [MeasurableSpace V]
    {A : Set V} {ω : ℕ → V} (h : ω 0 ∈ A) : 0 < exitTime A ω := by
  apply bot_lt_iff_ne_bot.mpr
  intro he
  have hle : exitTime A ω ≤ (0 : WithTop ℕ) := by simp [he]
  obtain ⟨n, hn, hout⟩ := (exitTime_le_iff A ω 0).mp hle
  have : n = 0 := Nat.eq_zero_of_le_zero hn
  exact hout (this ▸ h)

/-- Finite active stages have strictly increasing clocks if each selected
set contains its selecting vertex. -/
theorem actualWalkStage_active_clock_lt_of_select_mem
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (n k l : ℕ)
    (hselect : ∀ n v j, select n v = some j → v ∈ B j)
    (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l)
    (hactive : (actualWalkStage pos B initial select (n + 1) ω).2.1 = false) :
    k < l := by
  let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
  let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
  have hlast : (observedHistory τ ω).2 (observedHistory τ ω).1 = ω k := by
    rw [observedHistory_of_eq (show τ ω = k from hk)]
    simp [paddedHistory, frestrictLe_apply]
  have hsome : ∃ j, choice (observedHistory τ ω) = some j := by
    cases hj : choice (observedHistory τ ω) with
    | none =>
      change (selectedClockedExcursion pos B
        (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
        (futureAt τ ω)).1 = false at hactive
      simp [hj, selectedClockedExcursion] at hactive
    | some j => exact ⟨j, rfl⟩
  obtain ⟨j, hj⟩ := hsome
  have hsel : select n (ω k) = some j := by
    have hj' := hj
    simp only [choice, walkStageSelector] at hj'
    split at hj'
    · contradiction
    · simpa only [hlast] using hj'
  have hclock : (k : WithTop ℕ) + exitTime (B j) (walkShift k ω) = l := by
    have h := hl
    change nextSelectedExitTime τ B choice ω = l at h
    unfold nextSelectedExitTime at h
    rw [show τ ω = k from hk, hj, futureAt_of_eq (show τ ω = k from hk)] at h
    exact h
  have hexfin : exitTime (B j) (walkShift k ω) ≠ ⊤ := by
    intro he
    simp [he] at hclock
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hexfin
  have hkl : k + q = l := by
    rw [← hq] at hclock
    exact WithTop.coe_injective hclock
  have hqpos : 0 < q := by
    have h := exitTime_pos_of_mem (A := B j) (ω := walkShift k ω) (by
      simpa [walkShift] using hselect n (ω k) j hsel)
    rw [← hq] at h
    exact WithTop.coe_lt_coe.mp h
  omega

/-- Selected-set membership supplies the strictness assumptions of the
finite absorbed comparison clock. -/
theorem actualWalkStage_exists_absorbed_comparison_clock_of_select_mem
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (K : ℕ) (k : ℕ → ℕ)
    (hclock : ∀ i ≤ K, (actualWalkStage pos B initial select i ω).1 = k i)
    (hinit : ω 0 ∈ B initial)
    (hselect : ∀ n v j, select n v = some j → v ∈ B j) :
    ∃ T : ℕ → ℝ≥0, T 0 = 0 ∧ Monotone T ∧
      (∀ i ≤ K, T (i + 1) = k i) ∧
      (∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1)) := by
  apply actualWalkStage_exists_absorbed_comparison_clock pos B initial select ω K k hclock
  · have h := exitTime_pos_of_mem hinit
    change 0 < (actualWalkStage pos B initial select 0 ω).1 at h
    rw [hclock 0 (Nat.zero_le K)] at h
    exact WithTop.coe_lt_coe.mp h
  · intro i hi ha
    exact actualWalkStage_active_clock_lt_of_select_mem pos B initial select ω i (k i)
      (k (i + 1)) hselect (hclock i (by omega)) (hclock (i + 1) (by omega)) ha

end BouRabeeGwynne.FiniteConductanceNetwork
