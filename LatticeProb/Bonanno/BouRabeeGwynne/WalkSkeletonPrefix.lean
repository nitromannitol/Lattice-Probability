/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkSkeletonPrefix at commit fdb5cad; imports are relocated and a linter setting is added. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton
import LatticeProb.Bonanno.BouRabeeGwynne.WalkSkeletonLaw
import LatticeProb.Bonanno.BouRabeeGwynne.WalkExcursionRecovery
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionTrajectory

/-! Exact recovery of the finite excursion prefix of one original walk.
The monotone clock and all integer stage times are retained, even when the
total duration is zero. -/

open MeasureTheory Set
open scoped unitInterval

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

noncomputable def actualWalkStage_times (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V) :
    Fin (n + 2) → ℕ :=
  Fin.cases 0 (fun i => (actualWalkStage pos B initial select i.val ω).1.untopD 0)

lemma actualWalkStage_clock_finite_of_le (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V) {i n : ℕ}
    (hin : i ≤ n) (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    (actualWalkStage pos B initial select i ω).1 ≠ ⊤ :=
  ne_top_of_le_ne_top hfinite (actualWalkStage_clock_mono pos B initial select ω hin)

set_option linter.unusedSectionVars false in
private lemma actualWalkStage_clock_eq_coe (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (ω : ℕ → V) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    (actualWalkStage pos B initial select n ω).1 =
      (((actualWalkStage pos B initial select n ω).1.untopD 0 : ℕ) : WithTop ℕ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [← hm]
  rfl

lemma actualWalkStage_times_monotone (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    Monotone (actualWalkStage_times pos B initial select n ω) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact Nat.zero_le _
  · exact WithTop.untopD_mono
      (actualWalkStage_clock_finite_of_le pos B initial select ω (by omega) hfinite)
      (actualWalkStage_clock_mono pos B initial select ω (Nat.le_succ k.val))

lemma actualWalkStage_eq_segment_times (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤)
    (i : Fin (n + 1)) :
    (actualWalkStage pos B initial select i.val ω).2.2 =
      clockedWalkSegment pos ω
        (actualWalkStage_times pos B initial select n ω i.castSucc)
        (actualWalkStage_times pos B initial select n ω i.succ) := by
  have hc (k : ℕ) (hk : k ≤ n) := actualWalkStage_clock_eq_coe pos B initial select ω k
    (actualWalkStage_clock_finite_of_le pos B initial select ω hk hfinite)
  refine Fin.cases ?_ (fun k => ?_) i
  · exact actualWalkStage_zero_segment pos B initial select ω _ (hc 0 (Nat.zero_le n))
  · exact actualWalkStage_succ_segment pos B initial select k.val ω _ _
      (hc k.val (by omega)) (hc (k.val + 1) (by omega))

lemma actualWalkStage_compatiblePaths (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤) :
    (fun k => ClockedWalkExcursion.curve
      (actualWalkStage pos B initial select k ω).2.2) ∈
        ExcursionTrajectory.compatiblePaths n d := by
  intro i j hij
  change ClockedWalkExcursion.curve (actualWalkStage pos B initial select i.val ω).2.2 1 =
    ClockedWalkExcursion.curve (actualWalkStage pos B initial select j.val ω).2.2 0
  rw [actualWalkStage_eq_segment_times pos B initial select n ω hfinite i,
    actualWalkStage_eq_segment_times pos B initial select n ω hfinite j,
    ClockedWalkExcursion.curve_endPoint, ClockedWalkExcursion.curve_start]
  have hle := actualWalkStage_times_monotone pos B initial select n ω hfinite
    i.castSucc_lt_succ.le
  simp only [ClockedWalkExcursion.endPoint, ClockedWalkExcursion.start,
    clockedWalkSegment, min_self, min_eq_left (Nat.zero_le _), Nat.add_zero]
  rw [Nat.add_sub_of_le hle, hij]

/-- The actual pasted walk prefix is the original finite polygonal curve
composed with a continuous monotone clock. Its knots retain the exact integer
stage times; repeated times and zero total duration require no exception. -/
theorem actualWalkStage_concatenate_eq_comp (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤)
    (P : TimePartition n) :
    ∃ Q : WeakTimeKnots n,
      (∀ i, (((actualWalkStage pos B initial select n ω).1.untopD 0 : ℕ) : ℝ) *
        (Q.knots i : ℝ) = (actualWalkStage_times pos B initial select n ω i : ℝ)) ∧
      P.concatenate (ExcursionTrajectory.prefixChain n d
        (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial select k ω).2.2)) =
      (polygonalCurve pos ω ((actualWalkStage pos B initial select n ω).1.untopD 0)).comp
        (P.weakClock Q) := by
  let times := actualWalkStage_times pos B initial select n ω
  have hm : Monotone times := actualWalkStage_times_monotone pos B initial select n ω hfinite
  have hf : times 0 = 0 := rfl
  have hl : times (Fin.last (n + 1)) =
      (actualWalkStage pos B initial select n ω).1.untopD 0 := rfl
  obtain ⟨Q, hQ⟩ := exists_weakWalkTimeKnots P times hm hf hl
  refine ⟨Q, hQ, ?_⟩
  have hchain := clockedWalkSegments_eq_restrictChain Q pos ω times hm hl hQ
    (ExcursionTrajectory.prefixChain n d
      (fun k => ClockedWalkExcursion.curve (actualWalkStage pos B initial select k ω).2.2))
    (by
      intro i
      rw [ExcursionTrajectory.prefixChain_apply
        (actualWalkStage_compatiblePaths pos B initial select n ω hfinite)]
      exact congrArg ClockedWalkExcursion.curve
        (actualWalkStage_eq_segment_times pos B initial select n ω hfinite i))
  rw [hchain, WeakTimeKnots.concatenate_restrictChain]

/-- The same pointwise identity for the rich sequence used by the actual walk
law and coupling, with spatial selectors acting on each original endpoint. -/
theorem actualWalkExcursionSequence_concatenate_eq_comp (pos : V → Euc d)
    (B : J → Set V) (initial : J) (select : ℕ → Euc d → Option J)
    (n : ℕ) (ω : ℕ → V)
    (hfinite : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1 ≠ ⊤)
    (P : TimePartition n) :
    ∃ Q : WeakTimeKnots n,
      (∀ i, (((actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0 : ℕ) : ℝ) *
        (Q.knots i : ℝ) =
        (actualWalkStage_times pos B initial (fun i v => select i (pos v)) n ω i : ℝ)) ∧
      P.concatenate (ExcursionTrajectory.prefixChain n d
        (fun k => ClockedWalkExcursion.curve
          (actualWalkExcursionSequence pos B initial select ω k).2)) =
      (polygonalCurve pos ω
        ((actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).1.untopD 0)).comp
        (P.weakClock Q) :=
  actualWalkStage_concatenate_eq_comp pos B initial (fun i v => select i (pos v))
    n ω hfinite P

end BouRabeeGwynne.FiniteConductanceNetwork
