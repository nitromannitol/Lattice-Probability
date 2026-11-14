import LatticeProb.Walk.ActualSkeletonAbsorption
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Endpoints of discrete parent-block excursions -/

set_option autoImplicit false

open Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

/-- An active finite step starts in its selected square and ends outside the
corresponding parent-block interior. -/
theorem actualWalkStage_active_parentBlock_endpoints
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (centres : J → ℂ) (s : ℝ)
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm (pos v) ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (hB : ∀ j v, v ∉ B j → Complex.orthonormalBasisOneI.repr.symm (pos v) ∉
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (n : ℕ) (ω : ℕ → V)
    (hactive : (actualWalkStage pos B initial select (n + 1) ω).2.1 = false)
    (hfinite : (actualWalkStage pos B initial select (n + 1) ω).1 ≠ ⊤) :
    ∃ j, Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select n ω).2.2) ∈
          LatticeProb.ParentBlock.closedSquare (centres j) s ∧
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select (n + 1) ω).2.2) ∉
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s) := by
  have hp : (actualWalkStage pos B initial select n ω).1 ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ n))
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hp
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hfinite
  let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
  let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
  have hlast : (observedHistory τ ω).2 (observedHistory τ ω).1 = ω k := by
    rw [observedHistory_of_eq (show τ ω = k from hk.symm)]
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
    have h := hl.symm
    change nextSelectedExitTime τ B choice ω = l at h
    unfold nextSelectedExitTime at h
    rw [show τ ω = k from hk.symm, hj, futureAt_of_eq (show τ ω = k from hk.symm)] at h
    exact h
  have hexfin : exitTime (B j) (walkShift k ω) ≠ ⊤ := by
    intro he
    simp [he] at hclock
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hexfin
  have hkl : k + q = l := by
    rw [← hq] at hclock
    exact WithTop.coe_injective hclock
  have hexit := exitTime_mem_compl_of_ne_top hexfin
  rw [← hq] at hexit
  simp only [walkShift] at hexit
  change ω (k + q) ∉ B j at hexit
  refine ⟨j, ?_, ?_⟩
  · rw [actualWalkStage_endPoint_of_clock pos B initial select n ω k hk.symm]
    exact hselect n (ω k) j hsel
  · rw [actualWalkStage_endPoint_of_clock pos B initial select (n + 1) ω l hl.symm, ← hkl]
    exact hB j (ω (k + q)) hexit

/-- A finite active prefix admits one selected centre for each pair of
consecutive endpoints. -/
theorem actualWalkStage_parentBlock_endpoint_prefix
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc 2) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (centres : J → ℂ) (s : ℝ)
    (hselect : ∀ n v j, select n v = some j →
      Complex.orthonormalBasisOneI.repr.symm (pos v) ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (hB : ∀ j v, v ∉ B j → Complex.orthonormalBasisOneI.repr.symm (pos v) ∉
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (M : ℕ) (ω : ℕ → V)
    (hactive : ∀ n, n + 1 < M → (actualWalkStage pos B initial select (n + 1) ω).2.1 = false)
    (hfinite : (actualWalkStage pos B initial select M ω).1 ≠ ⊤) :
    ∃ c : ℕ → ℂ, ∀ n, n + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select n ω).2.2) ∈
          LatticeProb.ParentBlock.closedSquare (c n) s ∧
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select (n + 1) ω).2.2) ∉
          interior (LatticeProb.ParentBlock.parentBlock (c n) s) := by
  classical
  have h : ∀ n, ∃ j, n + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select n ω).2.2) ∈
          LatticeProb.ParentBlock.closedSquare (centres j) s ∧
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select (n + 1) ω).2.2) ∉
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s) := by
    intro n
    by_cases hn : n + 1 < M
    · have hf := ne_top_of_le_ne_top hfinite
        ((actualWalkStage_clock_mono pos B initial select ω) hn.le)
      obtain ⟨j, hs, he⟩ := actualWalkStage_active_parentBlock_endpoints
        pos B initial select centres s hselect hB n ω (hactive n hn) hf
      exact ⟨j, fun _ => ⟨hs, he⟩⟩
    · exact ⟨initial, fun hn' => False.elim (hn hn')⟩
  choose selected hselected using h
  exact ⟨fun n => centres (selected n), hselected⟩

end BouRabeeGwynne.FiniteConductanceNetwork
