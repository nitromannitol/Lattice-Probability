/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ActualWalkSkeleton at commit fdb5cad; local import paths are changed and linter settings are added. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkAdaptiveStopping
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSelectedRestart

/-! Successive rich excursions of one original ambient walk. Stage zero is
the actual first chosen-ball excursion. Elapsed clocks are never discarded. -/

open MeasureTheory ProbabilityTheory Set

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- The exact integer-time segment, with terminal padding. -/
def clockedWalkSegment (pos : V → Euc d) (ω : ℕ → V) (a b : ℕ) :
    ClockedWalkExcursion d :=
  (b - a, fun k => pos (ω (a + min k (b - a))))

lemma clockedWalkSegment_eq_of_prefix (pos : V → Euc d) {ω ω' : ℕ → V}
    {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n)
    (hp : Preorder.frestrictLe n ω = Preorder.frestrictLe n ω') :
    clockedWalkSegment pos ω a b = clockedWalkSegment pos ω' a b := by
  apply Prod.ext
  · rfl
  · funext k
    apply congrArg pos
    apply eval_eq_of_prefix_eq hp
    have := min_le_right k (b - a)
    omega

set_option linter.unusedSectionVars false in
lemma selectedClockedExcursion_snd_eq_segment (pos : V → Euc d) (B : J → Set V)
    (choice : Option J) (ω : ℕ → V) (k l : ℕ)
    (hclock : (k : WithTop ℕ) + (match choice with
      | none => 0
      | some j => exitTime (B j) (walkShift k ω)) = l) :
    (selectedClockedExcursion pos B (choice, ω k) (walkShift k ω)).2 =
      clockedWalkSegment pos ω k l := by
  cases choice with
  | none =>
    have hkl : k = l := by
      simp only [add_zero] at hclock
      exact_mod_cast hclock
    subst l
    simp [selectedClockedExcursion, clockedWalkSegment, ClockedWalkExcursion.constant]
  | some j =>
    change (k : WithTop ℕ) + exitTime (B j) (walkShift k ω) = (l : WithTop ℕ) at hclock
    cases he : exitTime (B j) (walkShift k ω) with
    | top => simp [he] at hclock
    | coe m =>
      have hkl : k + m = l := by
        rw [he] at hclock
        have hc : ((k + m : ℕ) : WithTop ℕ) = (l : WithTop ℕ) := by
          calc
            _ = (k : WithTop ℕ) + (m : WithTop ℕ) := rfl
            _ = _ := hclock
        exact WithTop.coe_injective hc
      subst l
      simp [selectedClockedExcursion, ClockedWalkExcursion.ofWalk, he,
        clockedWalkSegment, walkShift]

/-- Recompute the previous termination flag from the observed finite past.
The pathwise past-invariance lemma identifies it with the original flag. -/
def walkStageSelector (previous : (ℕ → V) → WithTop ℕ × (Bool × ClockedWalkExcursion d))
    (select : V → Option J) (h : ℕ × (ℕ → V)) : Option J :=
  if (previous h.2).2.1 = true then none else select (h.2 h.1)

/-- The actual original-path construction. A terminating selection yields a
constant excursion and the next stage retains its permanent stopped flag. -/
noncomputable def actualWalkStage (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) : ℕ → (ℕ → V) → WithTop ℕ × (Bool × ClockedWalkExcursion d)
  | 0, ω => (exitTime (B initial) ω, (false, ClockedWalkExcursion.ofWalk pos (B initial) ω))
  | n + 1, ω =>
    let previous := actualWalkStage pos B initial select n
    let τ := fun ξ => (previous ξ).1
    let choice := walkStageSelector previous (select n)
    let h := observedHistory τ ω
    (nextSelectedExitTime τ B choice ω,
      selectedClockedExcursion pos B (choice h, h.2 h.1) (futureAt τ ω))

set_option linter.unusedSectionVars false in
theorem actualWalkStage_clock_isStoppingTime (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => V))
      (fun ω => (actualWalkStage pos B initial select n ω).1) := by
  induction n with
  | zero => exact exitTime_isStoppingTime (B initial)
  | succ n ih =>
    exact isStoppingTime_nextSelectedExitTime ih B
      (walkStageSelector (actualWalkStage pos B initial select n) (select n))

set_option linter.unusedSectionVars false in
lemma actualWalkStage_zero_segment (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (m : ℕ)
    (hm : (actualWalkStage pos B initial select 0 ω).1 = m) :
    (actualWalkStage pos B initial select 0 ω).2.2 = clockedWalkSegment pos ω 0 m := by
  change exitTime (B initial) ω = m at hm
  change ClockedWalkExcursion.ofWalk pos (B initial) ω = _
  simp [ClockedWalkExcursion.ofWalk, hm, clockedWalkSegment]

lemma actualWalkStage_succ_segment (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V) (k l : ℕ)
    (hk : (actualWalkStage pos B initial select n ω).1 = k)
    (hl : (actualWalkStage pos B initial select (n + 1) ω).1 = l) :
    (actualWalkStage pos B initial select (n + 1) ω).2.2 =
      clockedWalkSegment pos ω k l := by
  let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
  let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
  have hlast : (observedHistory τ ω).2 (observedHistory τ ω).1 = ω k := by
    rw [observedHistory_of_eq (show τ ω = k from hk)]
    simp [paddedHistory, Preorder.frestrictLe_apply]
  have hclock : (k : WithTop ℕ) + (match choice (observedHistory τ ω) with
      | none => 0
      | some j => exitTime (B j) (walkShift k ω)) = l := by
    change nextSelectedExitTime τ B choice ω = l at hl
    unfold nextSelectedExitTime at hl
    rw [show τ ω = k from hk, futureAt_of_eq (show τ ω = k from hk)] at hl
    exact hl
  change (selectedClockedExcursion pos B
    (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
    (futureAt τ ω)).2 = _
  rw [hlast, futureAt_of_eq (show τ ω = k from hk)]
  exact selectedClockedExcursion_snd_eq_segment pos B (choice (observedHistory τ ω)) ω k l hclock

set_option linter.unusedSectionVars false in
lemma measurable_walkStageSelector
    {previous : (ℕ → V) → WithTop ℕ × (Bool × ClockedWalkExcursion d)}
    (hp : Measurable previous) (select : V → Option J) :
    Measurable (walkStageSelector previous select) := by
  unfold walkStageSelector
  exact Measurable.ite
    (measurableSet_eq_fun (hp.snd.fst.comp measurable_snd) measurable_const)
    measurable_const ((measurable_of_finite select).comp measurable_historyLast)

theorem measurable_actualWalkStage (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) :
    Measurable (actualWalkStage pos B initial select n) := by
  induction n with
  | zero =>
    exact (exitTime_isStoppingTime (B initial)).measurable'.prodMk
      (measurable_const.prodMk (ClockedWalkExcursion.measurable_ofWalk pos (B initial)))
  | succ n ih =>
    let τ := fun ω => (actualWalkStage pos B initial select n ω).1
    have hτ : Measurable τ := (actualWalkStage_clock_isStoppingTime pos B initial select n).measurable'
    have hobs := measurable_observedHistory hτ
    have hchoice := measurable_walkStageSelector ih (select n)
    have hparameters : Measurable (fun ω =>
        (walkStageSelector (actualWalkStage pos B initial select n) (select n)
          (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)) :=
      (hchoice.comp hobs).prodMk (measurable_historyLast.comp hobs)
    exact (actualWalkStage_clock_isStoppingTime pos B initial select (n + 1)).measurable'.prodMk
      ((measurable_selectedClockedExcursion pos B).comp
        (hparameters.prodMk (measurable_futureAt hτ)))

set_option linter.unusedSectionVars false in
lemma actualWalkStage_clock_mono (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V) :
    Monotone (fun n => (actualWalkStage pos B initial select n ω).1) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_nextSelectedExitTime
    (fun ξ => (actualWalkStage pos B initial select n ξ).1) B
    (walkStageSelector (actualWalkStage pos B initial select n) (select n)) ω

lemma actualWalkStage_flag_eq_of_prefix (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i n : ℕ) {ω ω' : ℕ → V}
    (hp : Preorder.frestrictLe n ω = Preorder.frestrictLe n ω')
    (ht : (actualWalkStage pos B initial select i ω).1 ≤ n) :
    (actualWalkStage pos B initial select i ω).2.1 =
      (actualWalkStage pos B initial select i ω').2.1 := by
  cases i with
  | zero => rfl
  | succ i =>
    let τ := fun ξ => (actualWalkStage pos B initial select i ξ).1
    let choice := walkStageSelector (actualWalkStage pos B initial select i) (select i)
    have hτn : τ ω ≤ n :=
      ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ i)).trans ht
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hτn)
    have hkn : k ≤ n := (WithTop.coe_le_coe (α := ℕ)).mp (hk.trans_le hτn)
    have hobs := observedHistory_eq_of_prefix_eq
      (actualWalkStage_clock_isStoppingTime pos B initial select i) hp hkn hk.symm
    change (selectedClockedExcursion pos B
      (choice (observedHistory τ ω), (observedHistory τ ω).2 (observedHistory τ ω).1)
      (futureAt τ ω)).1 =
      (selectedClockedExcursion pos B
      (choice (observedHistory τ ω'), (observedHistory τ ω').2 (observedHistory τ ω').1)
      (futureAt τ ω')).1
    rw [← hobs]
    cases choice (observedHistory τ ω) <;> rfl

/-- The full clock, flag, duration and all padded vertices of an observed
excursion depend only on the original path up to its elapsed clock. -/
lemma actualWalkStage_eq_of_prefix (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i n : ℕ) {ω ω' : ℕ → V}
    (hp : Preorder.frestrictLe n ω = Preorder.frestrictLe n ω')
    (ht : (actualWalkStage pos B initial select i ω).1 ≤ n) :
    actualWalkStage pos B initial select i ω = actualWalkStage pos B initial select i ω' := by
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top ht)
  have hln : l ≤ n := (WithTop.coe_le_coe (α := ℕ)).mp (hl.trans_le ht)
  have hl' := stopping_eq_of_prefix_eq
    (actualWalkStage_clock_isStoppingTime pos B initial select i) hp hln hl.symm
  apply Prod.ext
  · exact hl.symm.trans hl'.symm
  apply Prod.ext
  · exact actualWalkStage_flag_eq_of_prefix pos B initial select i n hp ht
  cases i with
  | zero =>
    rw [actualWalkStage_zero_segment pos B initial select ω l hl.symm,
      actualWalkStage_zero_segment pos B initial select ω' l hl']
    exact clockedWalkSegment_eq_of_prefix pos (Nat.zero_le l) hln hp
  | succ i =>
    have hprev : (actualWalkStage pos B initial select i ω).1 ≤ (l : WithTop ℕ) :=
      ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ i)).trans_eq hl.symm
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hprev)
    have hkl : k ≤ l := (WithTop.coe_le_coe (α := ℕ)).mp (hk.trans_le hprev)
    have hk' := stopping_eq_of_prefix_eq
      (actualWalkStage_clock_isStoppingTime pos B initial select i) hp (hkl.trans hln) hk.symm
    rw [actualWalkStage_succ_segment pos B initial select i ω k l hk.symm hl.symm,
      actualWalkStage_succ_segment pos B initial select i ω' k l hk' hl']
    exact clockedWalkSegment_eq_of_prefix pos hkl hln hp

lemma actualWalkStage_observedPast (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select i ω).1 ≠ ⊤) :
    actualWalkStage pos B initial select i
      (observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).2 =
      actualWalkStage pos B initial select i ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hp : Preorder.frestrictLe k ω = Preorder.frestrictLe k
      (observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).2 := by
    rw [observedHistory_of_eq hk.symm]
    funext j
    simp only [paddedHistory, Preorder.frestrictLe_apply,
      Nat.min_eq_left (Finset.mem_Iic.mp j.property)]
  exact (actualWalkStage_eq_of_prefix pos B initial select i k hp hk.symm.le).symm

lemma actualWalkStage_stopped_permanent (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select i ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select i ω).2.1 = true) :
    (actualWalkStage pos B initial select (i + 1) ω).2.1 = true := by
  let τ := fun ξ => (actualWalkStage pos B initial select i ξ).1
  let h := observedHistory τ ω
  have hflag : (actualWalkStage pos B initial select i h.2).2.1 = true := by
    rw [actualWalkStage_observedPast pos B initial select i ω hfin]
    exact hstop
  have hchoice : walkStageSelector (actualWalkStage pos B initial select i) (select i) h = none := by
    simp only [walkStageSelector, hflag, ↓reduceIte]
  change (selectedClockedExcursion pos B
    (walkStageSelector (actualWalkStage pos B initial select i) (select i) h, h.2 h.1)
    (futureAt τ ω)).1 = true
  rw [hchoice]
  rfl

set_option linter.unusedSectionVars false in
lemma actualWalkStage_clock_le_ambientExit (pos : V → Euc d) {A : Set V}
    (B : J → Set V) (hBA : ∀ j, B j ⊆ A) (initial : J)
    (select : ℕ → V → Option J) (ω : ℕ → V) (n : ℕ) :
    (actualWalkStage pos B initial select n ω).1 ≤ exitTime A ω := by
  induction n with
  | zero => exact exitTime_le_of_subset (hBA initial) ω
  | succ n ih =>
    exact nextSelectedExitTime_le_exitTime
      (fun ξ => (actualWalkStage pos B initial select n ξ).1) B hBA
      (walkStageSelector (actualWalkStage pos B initial select n) (select n)) ω ih

/-- All actual recursive clocks are finite on one common probability-one
event, derived from the finite ambient walk rather than postulated per stage. -/
theorem actualWalkStage_ae_all_clocks_finite (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (select : ℕ → V → Option J) (v : V) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ n,
      (actualWalkStage pos B initial select n ω).1 ≠ ⊤ := by
  filter_upwards [N.trajectoryLaw_ae_finiteExit A hA haccess v] with ω hω
  intro n
  exact ne_top_of_le_ne_top hω
    (actualWalkStage_clock_le_ambientExit pos B hBA initial select ω n)

end BouRabeeGwynne.FiniteConductanceNetwork
