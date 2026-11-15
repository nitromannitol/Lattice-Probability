import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton

/-! # Pre-exit containment for successive walk stages -/

set_option autoImplicit false

open Preorder

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- Before the initial stage ends, the walk stays in the initial set. -/
theorem actualWalkStage_zero_mem_before_clock
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (l m : ℕ)
    (hl : (actualWalkStage pos B initial select 0 ω).1 = l) (hm : m < l) :
    ω m ∈ B initial := by
  apply mem_of_lt_exitTime
  change (m : WithTop ℕ) < (actualWalkStage pos B initial select 0 ω).1
  rw [hl]
  exact_mod_cast hm

/-- A finite active successor stage selects a set containing every walk vertex
from its starting clock up to, but excluding, its endpoint clock. -/
theorem actualWalkStage_active_pre_exit
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (n k l : ℕ)
    (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l)
    (hactive : (actualWalkStage pos B initial select (n + 1) ω).2.1 = false) :
    ∃ j, select n (ω k) = some j ∧ ∀ m, k ≤ m → m < l → ω m ∈ B j := by
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
  have hfin : exitTime (B j) (walkShift k ω) ≠ ⊤ := by
    intro he
    simp [he] at hclock
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hkl : k + q = l := by
    rw [← hq] at hclock
    exact WithTop.coe_injective hclock
  refine ⟨j, hsel, ?_⟩
  intro m hkm hml
  have hmq : m - k < q := by omega
  have hm : (walkShift k ω) (m - k) ∈ B j := by
    apply mem_of_lt_exitTime
    rw [← hq]
    exact (WithTop.coe_lt_coe).2 hmq
  simpa only [walkShift, Nat.add_sub_of_le hkm] using hm

end BouRabeeGwynne.FiniteConductanceNetwork
