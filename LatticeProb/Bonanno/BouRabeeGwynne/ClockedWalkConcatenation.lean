/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ClockedWalkConcatenation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton

/-! Measurable reconstruction of the complete padded vertex sequence from
finitely many rich excursions. The concatenation retains integer duration. -/

open MeasureTheory Set

namespace BouRabeeGwynne.ClockedWalkExcursion

variable {d : ℕ}

def append (e f : ClockedWalkExcursion d) : ClockedWalkExcursion d :=
  (e.1 + f.1, fun k => if k ≤ e.1 then e.2 k else f.2 (k - e.1))

lemma measurable_append : Measurable (fun p : ClockedWalkExcursion d × ClockedWalkExcursion d =>
    append p.1 p.2) := by
  apply Measurable.prodMk
  · exact measurable_fst.fst.add measurable_snd.fst
  · apply Measurable.of_eval
    intro k
    have hl : Measurable (fun p : ClockedWalkExcursion d × ClockedWalkExcursion d => p.1.2 k) :=
      (measurable_pi_apply k).comp measurable_fst.snd
    have hi : Measurable (fun p : ClockedWalkExcursion d × ClockedWalkExcursion d => k - p.1.1) :=
      (measurable_of_countable (fun n : ℕ => k - n)).comp measurable_fst.fst
    have hr : Measurable (fun p : ClockedWalkExcursion d × ClockedWalkExcursion d =>
        p.2.2 (k - p.1.1)) :=
      measurable_endPoint.comp (hi.prodMk measurable_snd.snd)
    exact hl.piecewise (measurableSet_le measurable_const measurable_fst.fst) hr

def concatenate (e : ℕ → ClockedWalkExcursion d) : ℕ → ClockedWalkExcursion d
  | 0 => e 0
  | n + 1 => append (concatenate e n) (e (n + 1))

lemma measurable_concatenate (n : ℕ) :
    Measurable (fun e : ℕ → ClockedWalkExcursion d => concatenate e n) := by
  induction n with
  | zero => exact measurable_pi_apply 0
  | succ n ih => exact measurable_append.comp (ih.prodMk (measurable_pi_apply (n + 1)))

lemma append_clockedWalkSegment {V : Type*} (pos : V → Euc d) (ω : ℕ → V)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    append (FiniteConductanceNetwork.clockedWalkSegment pos ω a b)
      (FiniteConductanceNetwork.clockedWalkSegment pos ω b c) =
        FiniteConductanceNetwork.clockedWalkSegment pos ω a c := by
  apply Prod.ext
  · change b - a + (c - b) = c - a
    omega
  · funext k
    change (if k ≤ b - a then pos (ω (a + min k (b - a)))
      else pos (ω (b + min (k - (b - a)) (c - b)))) = pos (ω (a + min k (c - a)))
    split_ifs with hk
    · apply congrArg (fun j : ℕ => pos (ω j))
      omega
    · apply congrArg (fun j : ℕ => pos (ω j))
      omega

theorem concatenate_of_clockedWalkSegments {V : Type*} (pos : V → Euc d) (ω : ℕ → V)
    (e : ℕ → ClockedWalkExcursion d) (times : ℕ → ℕ)
    (hmono : Monotone times) (hfirst : times 0 = 0) (n : ℕ) :
    (∀ i ≤ n, e i = FiniteConductanceNetwork.clockedWalkSegment pos ω (times i) (times (i + 1))) →
      concatenate e n = FiniteConductanceNetwork.clockedWalkSegment pos ω 0 (times (n + 1)) := by
  induction n with
  | zero =>
    intro hp
    simpa only [concatenate, hfirst] using hp 0 le_rfl
  | succ n ih =>
    intro hp
    rw [concatenate, ih (fun i hi => hp i (hi.trans (Nat.le_succ n))), hp (n + 1) le_rfl]
    exact append_clockedWalkSegment pos ω (Nat.zero_le _) (hmono (Nat.le_succ (n + 1)))

end BouRabeeGwynne.ClockedWalkExcursion
