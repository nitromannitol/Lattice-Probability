/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSkeletonObservation at commit fdb5cad; local import paths are changed and a scoped linter setting is added. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton

/-! Recover the whole finite excursion prefix and its current vertex from
the observed past of the same original walk. -/

open MeasureTheory ProbabilityTheory Set Preorder

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

set_option linter.unusedSectionVars false in
lemma clockedWalkSegment_endPoint (pos : V → Euc d) (ω : ℕ → V) {a b : ℕ}
    (hab : a ≤ b) : ClockedWalkExcursion.endPoint (clockedWalkSegment pos ω a b) = pos (ω b) := by
  simp [ClockedWalkExcursion.endPoint, clockedWalkSegment, Nat.add_sub_of_le hab]

lemma actualWalkStage_endPoint_of_clock (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i : ℕ) (ω : ℕ → V) (l : ℕ)
    (hl : (actualWalkStage pos B initial select i ω).1 = l) :
    ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select i ω).2.2 = pos (ω l) := by
  cases i with
  | zero =>
    rw [actualWalkStage_zero_segment pos B initial select ω l hl]
    exact clockedWalkSegment_endPoint pos ω (Nat.zero_le l)
  | succ i =>
    have hprev : (actualWalkStage pos B initial select i ω).1 ≤ (l : WithTop ℕ) :=
      ((actualWalkStage_clock_mono pos B initial select ω) (Nat.le_succ i)).trans_eq hl
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top WithTop.coe_ne_top hprev)
    have hkl : k ≤ l := (WithTop.coe_le_coe (α := ℕ)).mp (hk.trans_le hprev)
    rw [actualWalkStage_succ_segment pos B initial select i ω k l hk.symm hl]
    exact clockedWalkSegment_endPoint pos ω hkl

lemma actualWalkStage_endPoint_observed (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (i : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select i ω).1 ≠ ⊤) :
    ClockedWalkExcursion.endPoint (actualWalkStage pos B initial select i ω).2.2 =
      pos ((observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).2
        (observedHistory (fun ξ => (actualWalkStage pos B initial select i ξ).1) ω).1) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [observedHistory_of_eq hk.symm]
  simpa only [paddedHistory, frestrictLe_apply, min_self] using
    actualWalkStage_endPoint_of_clock pos B initial select i ω k hk.symm

/-- Recompute every earlier rich excursion from a supplied observed past. -/
noncomputable def walkSkeletonPrefixOfPast (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (h : ℕ × (ℕ → V)) :
    Finset.Iic n → Bool × ClockedWalkExcursion d :=
  fun i => (actualWalkStage pos B initial select i.val h.2).2

lemma measurable_walkSkeletonPrefixOfPast (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) :
    Measurable (walkSkeletonPrefixOfPast pos B initial select n) :=
  Measurable.of_eval fun i =>
    (measurable_actualWalkStage pos B initial select i.val).snd.comp measurable_snd

/-- Recovery holds for the entire observed excursion prefix, not only for
its final endpoint or its most recent state. -/
lemma walkSkeletonPrefixOfPast_observed (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfin : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    walkSkeletonPrefixOfPast pos B initial select n
      (observedHistory (fun ξ => (actualWalkStage pos B initial select n ξ).1) ω) =
        frestrictLe n (fun i => (actualWalkStage pos B initial select i ω).2) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hp : frestrictLe k ω = frestrictLe k
      (observedHistory (fun ξ => (actualWalkStage pos B initial select n ξ).1) ω).2 := by
    rw [observedHistory_of_eq hk.symm]
    funext j
    simp only [paddedHistory, frestrictLe_apply,
      Nat.min_eq_left (Finset.mem_Iic.mp j.property)]
  funext i
  have ht : (actualWalkStage pos B initial select i.val ω).1 ≤ (k : WithTop ℕ) :=
    ((actualWalkStage_clock_mono pos B initial select ω)
      (Finset.mem_Iic.mp i.property)).trans_eq hk.symm
  exact congrArg Prod.snd (actualWalkStage_eq_of_prefix pos B initial select i.val k hp ht).symm

end BouRabeeGwynne.FiniteConductanceNetwork
