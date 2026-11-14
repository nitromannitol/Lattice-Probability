/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkAdaptiveStopping at commit fdb5cad; local import paths are changed and linter settings are added. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStrongMarkov

/-! The next exit from a domain chosen from the actual observed walk history
is a stopping time. The possible infinite value is retained throughout. -/

open MeasureTheory ProbabilityTheory Set Preorder

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

set_option linter.unusedSectionVars false in
lemma eval_eq_of_prefix_eq {n k : ℕ} {ω ω' : ℕ → V}
    (h : frestrictLe n ω = frestrictLe n ω') (hk : k ≤ n) : ω k = ω' k :=
  congrFun h ⟨k, Finset.mem_Iic.mpr hk⟩

lemma prefix_eq_of_prefix_eq {n k : ℕ} {ω ω' : ℕ → V}
    (h : frestrictLe n ω = frestrictLe n ω') (hk : k ≤ n) :
    frestrictLe k ω = frestrictLe k ω' := by
  funext i
  exact eval_eq_of_prefix_eq h ((Finset.mem_Iic.mp i.property).trans hk)

lemma stopping_eq_of_prefix_eq {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    {n k : ℕ} {ω ω' : ℕ → V} (h : frestrictLe n ω = frestrictLe n ω')
    (hk : k ≤ n) (hω : τ ω = k) : τ ω' = k := by
  obtain ⟨s, _, hs⟩ := stopping_event_prefix hτ k
  have hm : frestrictLe k ω ∈ s := by
    change ω ∈ frestrictLe k ⁻¹' s
    rw [hs]
    exact hω
  have hm' : frestrictLe k ω' ∈ s :=
    (prefix_eq_of_prefix_eq h hk) ▸ hm
  change ω' ∈ {ω | τ ω = k}
  rw [← hs]
  exact hm'

lemma observedHistory_eq_of_prefix_eq {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    {n k : ℕ} {ω ω' : ℕ → V} (h : frestrictLe n ω = frestrictLe n ω')
    (hk : k ≤ n) (hω : τ ω = k) : observedHistory τ ω = observedHistory τ ω' := by
  rw [observedHistory_of_eq hω,
    observedHistory_of_eq (stopping_eq_of_prefix_eq hτ h hk hω),
    prefix_eq_of_prefix_eq h hk]

/-- In a finite state space, dependence only on the observed finite prefix
proves the canonical stopping-time condition. -/
lemma isStoppingTime_of_prefix_invariant {τ : (ℕ → V) → WithTop ℕ}
    (h : ∀ n ω ω', frestrictLe n ω = frestrictLe n ω' →
      (τ ω ≤ n ↔ τ ω' ≤ n)) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ := by
  intro n
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let s : Set (Finset.Iic n → V) := {p | τ (paddedHistory n p).2 ≤ n}
  refine ⟨s, s.toFinite.measurableSet, ?_⟩
  ext ω
  change τ (paddedHistory n (frestrictLe n ω)).2 ≤ n ↔ τ ω ≤ n
  apply h
  funext i
  simp only [paddedHistory, frestrictLe_apply,
    Nat.min_eq_left (Finset.mem_Iic.mp i.property)]

set_option linter.unusedSectionVars false in
lemma add_exitTime_shift_le_iff (B : Set V) (ω : ℕ → V) (k n : ℕ) :
    (k : WithTop ℕ) + exitTime B (walkShift k ω) ≤ n ↔
      ∃ l : ℕ, k + l ≤ n ∧ ω (k + l) ∉ B := by
  constructor
  · intro h
    cases he : exitTime B (walkShift k ω) with
    | top => simp only [he, add_top, top_le_iff] at h; exact (WithTop.coe_ne_top h).elim
    | coe l =>
      have hkl : k + l ≤ n := by
        rw [he] at h
        have hc : ((k + l : ℕ) : WithTop ℕ) ≤ (n : WithTop ℕ) := by
          calc
            _ = (k : WithTop ℕ) + (l : WithTop ℕ) := rfl
            _ ≤ _ := h
        exact (WithTop.coe_le_coe (α := ℕ)).mp hc
      obtain ⟨j, hj, hjB⟩ := (exitTime_le_iff B (walkShift k ω) l).mp he.le
      exact ⟨j, (Nat.add_le_add_left hj k).trans hkl, hjB⟩
  · rintro ⟨l, hkl, hl⟩
    have he : exitTime B (walkShift k ω) ≤ (l : WithTop ℕ) :=
      (exitTime_le_iff B (walkShift k ω) l).mpr ⟨l, le_rfl, hl⟩
    calc
      _ ≤ (k : WithTop ℕ) + l := add_le_add le_rfl he
      _ = ((k + l : ℕ) : WithTop ℕ) := (WithTop.coe_add _ _).symm
      _ ≤ n := WithTop.coe_le_coe.mpr hkl

/-- The selector can inspect the entire observed history. `none` terminates
at the current time; `some j` runs to the next actual vertex exit from `B j`. -/
noncomputable def nextSelectedExitTime (τ : (ℕ → V) → WithTop ℕ)
    (B : J → Set V) (select : (ℕ × (ℕ → V)) → Option J) (ω : ℕ → V) : WithTop ℕ :=
  τ ω + match select (observedHistory τ ω) with
    | none => 0
    | some j => exitTime (B j) (futureAt τ ω)

set_option linter.unusedSectionVars false in
lemma le_nextSelectedExitTime (τ : (ℕ → V) → WithTop ℕ)
    (B : J → Set V) (select : (ℕ × (ℕ → V)) → Option J) (ω : ℕ → V) :
    τ ω ≤ nextSelectedExitTime τ B select ω :=
  le_add_of_nonneg_right (by exact bot_le)

/-- Adaptive ball selection from the past gives an actual discrete stopping
time, without requiring finite exits on every sample path. -/
theorem isStoppingTime_nextSelectedExitTime {τ : (ℕ → V) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V)) τ)
    (B : J → Set V) (select : (ℕ × (ℕ → V)) → Option J) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
      (nextSelectedExitTime τ B select) := by
  apply isStoppingTime_of_prefix_invariant
  have transfer (n : ℕ) (ω ω' : ℕ → V)
      (hp : frestrictLe n ω = frestrictLe n ω')
      (ht : nextSelectedExitTime τ B select ω ≤ n) :
      nextSelectedExitTime τ B select ω' ≤ n := by
    have hle : τ ω ≤ n := (le_nextSelectedExitTime τ B select ω).trans ht
    have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hkn : k ≤ n := by
      rw [← hk] at hle
      exact WithTop.coe_le_coe.mp hle
    have hk' : τ ω' = k := stopping_eq_of_prefix_eq hτ hp hkn hk.symm
    have hobs : observedHistory τ ω = observedHistory τ ω' :=
      observedHistory_eq_of_prefix_eq hτ hp hkn hk.symm
    unfold nextSelectedExitTime at ht ⊢
    rw [hk', ← hobs]
    rw [← hk] at ht
    cases hs : select (observedHistory τ ω) with
    | none =>
      simp only [add_zero]
      exact (WithTop.coe_le_coe (α := ℕ)).mpr hkn
    | some j =>
      simp only [hs] at ht ⊢
      rw [futureAt_of_eq hk']
      rw [futureAt_of_eq hk.symm] at ht
      obtain ⟨l, hl, hbad⟩ := (add_exitTime_shift_le_iff (B j) ω k n).mp ht
      apply (add_exitTime_shift_le_iff (B j) ω' k n).mpr
      exact ⟨l, hl, (eval_eq_of_prefix_eq hp hl) ▸ hbad⟩
  intro n ω ω' hp
  exact ⟨transfer n ω ω' hp, transfer n ω' ω hp.symm⟩

set_option linter.unusedSectionVars false in
lemma exitTime_le_of_subset {A B : Set V} (hBA : B ⊆ A) (ω : ℕ → V) :
    exitTime B ω ≤ exitTime A ω := by
  by_cases hfin : exitTime A ω = ⊤
  · rw [hfin]
    exact le_top
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hn]
  obtain ⟨k, hk, hbad⟩ := (exitTime_le_iff A ω n).mp hn.symm.le
  exact (exitTime_le_iff B ω n).mpr ⟨k, hk, fun h => hbad (hBA h)⟩

/-- Every adaptive inner-domain exit precedes the original ambient vertex
exit. Hence almost-sure finiteness of all clocks follows from ambient exit. -/
lemma nextSelectedExitTime_le_exitTime (τ : (ℕ → V) → WithTop ℕ)
    {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (select : (ℕ × (ℕ → V)) → Option J) (ω : ℕ → V)
    (hτ : τ ω ≤ exitTime A ω) :
    nextSelectedExitTime τ B select ω ≤ exitTime A ω := by
  cases ha : exitTime A ω with
  | top => exact le_top
  | coe a =>
    have hbound : τ ω ≤ (a : WithTop ℕ) := hτ.trans_eq ha
    have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hbound
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hka : k ≤ a := by
      rw [← hk] at hbound
      exact WithTop.coe_le_coe.mp hbound
    unfold nextSelectedExitTime
    rw [← hk]
    cases hj : select (observedHistory τ ω) with
    | none =>
      simp only [add_zero]
      exact (WithTop.coe_le_coe (α := ℕ)).mpr hka
    | some j =>
      rw [futureAt_of_eq hk.symm]
      calc
        _ ≤ (k : WithTop ℕ) + exitTime A (walkShift k ω) :=
          add_le_add le_rfl (exitTime_le_of_subset (hBA j) (walkShift k ω))
        _ = (k : WithTop ℕ) + ((a - k : ℕ) : WithTop ℕ) := by
          rw [exitTime_walkShift_of_eq A ω ha hka]
        _ = (a : WithTop ℕ) :=
          congrArg (fun m : ℕ => (m : WithTop ℕ)) (Nat.add_sub_of_le hka)

end BouRabeeGwynne.FiniteConductanceNetwork
