/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkPathStopping at commit fdb5cad; local imports are rewritten and toolchain compatibility adjustments are applied. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedHistory

/-! Actual discrete path stopping, defined recursively without altering an
infinite exit time. The finite-history maps will identify absorption in a ball
with stopping the original ambient walk at its first ball exit. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped Classical

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Fintype V]

/-- Retain the original vertices until the first exit and then retain that
exit vertex forever. A path that never exits is unchanged. -/
noncomputable def stoppedWalkPath (B : Set V) (ω : ℕ → V) : ℕ → V := by
  classical
  exact Nat.rec (ω 0) (fun n z => if z ∈ B then ω (n + 1) else z)

set_option linter.unusedSectionVars false in
@[simp] lemma stoppedWalkPath_zero (B : Set V) (ω : ℕ → V) :
    stoppedWalkPath B ω 0 = ω 0 := rfl

set_option linter.unusedSectionVars false in
lemma stoppedWalkPath_succ (B : Set V) (ω : ℕ → V) (n : ℕ) :
    stoppedWalkPath B ω (n + 1) =
      if stoppedWalkPath B ω n ∈ B then ω (n + 1) else stoppedWalkPath B ω n := by
  classical
  rfl

lemma measurable_stoppedWalkPath (B : Set V) : Measurable (stoppedWalkPath B) := by
  classical
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_pi_apply 0
  | succ n ih =>
    simp only [stoppedWalkPath_succ]
    exact Measurable.ite (ih (Set.toFinite B).measurableSet) (measurable_pi_apply _) ih

lemma stoppedWalkPath_mem_imp_eq (B : Set V) (ω : ℕ → V) (n : ℕ)
    (hn : stoppedWalkPath B ω n ∈ B) : stoppedWalkPath B ω n = ω n := by
  classical
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hp : stoppedWalkPath B ω n ∈ B
    · simp only [stoppedWalkPath_succ, hp, ite_eq_left]
    · simp only [stoppedWalkPath_succ, hp] at hn
      exact (hp hn).elim

lemma stoppedWalkPath_eq_of_le_exitTime (B : Set V) (ω : ℕ → V) (n : ℕ)
    (hn : (n : WithTop ℕ) ≤ exitTime B ω) : stoppedWalkPath B ω n = ω n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : (n : WithTop ℕ) < exitTime B ω :=
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)).trans_le hn
    have hp := ih hlt.le
    rw [stoppedWalkPath_succ, hp, ite_eq_left (mem_of_lt_exitTime hlt)]

lemma stoppedWalkPath_after_not_mem (B : Set V) (ω : ℕ → V) {n : ℕ}
    (hn : stoppedWalkPath B ω n ∉ B) (k : ℕ) :
    stoppedWalkPath B ω (n + k) = stoppedWalkPath B ω n := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    change stoppedWalkPath B ω (n + k + 1) = _
    rw [stoppedWalkPath_succ, ih, ite_eq_right hn]

lemma stoppedWalkPath_congr_prefix (B : Set V) {ω ξ : ℕ → V} {n : ℕ}
    (h : ∀ k ≤ n, ω k = ξ k) :
    ∀ k ≤ n, stoppedWalkPath B ω k = stoppedWalkPath B ξ k := by
  classical
  intro k
  induction k with
  | zero => intro _; exact h 0 (Nat.zero_le n)
  | succ k ih =>
    intro hk
    rw [stoppedWalkPath_succ, stoppedWalkPath_succ, ih (Nat.le_of_succ_le hk), h _ hk]

/-- Stop a finite history, encoded by terminal padding only for evaluation. -/
noncomputable def stopHistory (B : Set V) (n : ℕ) (h : Finset.Iic n → V) :
    Finset.Iic n → V := frestrictLe n (stoppedWalkPath B (paddedHistory n h).2)

lemma measurable_stopHistory (B : Set V) (n : ℕ) : Measurable (stopHistory B n) :=
  measurable_of_finite _

lemma stopHistory_prefix (B : Set V) (n : ℕ) (ω : ℕ → V) :
    stopHistory B n (frestrictLe n ω) = frestrictLe n (stoppedWalkPath B ω) := by
  funext i
  apply stoppedWalkPath_congr_prefix B (n := n) _ i.val (Finset.mem_Iic.mp i.property)
  intro k hk
  change ω (min k n) = ω k
  rw [min_eq_left hk]

end BouRabeeGwynne.FiniteConductanceNetwork
