import LatticeProb.Prob.OpenEntryTimeTop
import LatticeProb.Prob.ClosedExitTimeTop

/-! # Measurable alternating entry and exit times -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Entry into an open set at or after an extended-real time, with `⊤` as the
value for an infinite starting time or absence of a hit. -/
noncomputable def openEntryAfter {Ω E : Type*} (f : Ω → ℝ → E)
    (a : Ω → WithTop ℝ) (U : Set E) (ω : Ω) : WithTop ℝ :=
  if a ω = ⊤ then ⊤ else
    hittingAfter (fun t ω => f ω t) U ((a ω).untopD 0) ω

/-- The initial clock and successive exit clocks, with open entries between them. -/
noncomputable def alternatingExitClock {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    (U V : Set (EuclideanSpace ℝ (Fin d))) : ℕ → Ω → WithTop ℝ
  | 0 => a
  | n + 1 => closedExitAfter f (openEntryAfter (fun ω t => f ω t)
      (alternatingExitClock f a U V n) U) V

/-- Every entry and exit clock in the alternating sequence is measurable. -/
theorem measurable_alternatingExitClock {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) (ha : Measurable a) (n : ℕ) :
    Measurable (alternatingExitClock f a U V n) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
      apply measurable_closedExitAfter f _ hV hf
      exact measurable_open_hittingAfter_top (fun ω t => f ω t) _ hU
        (fun ω => (f ω).continuous)
        (fun q => (continuous_eval_const (q : ℝ)).measurable.comp hf) ih

/-- Every open entry following an exit clock is measurable. -/
theorem measurable_alternatingEntryClock {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hf : Measurable f) (ha : Measurable a) (n : ℕ) :
    Measurable (openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U) := by
  exact measurable_open_hittingAfter_top (fun ω t => f ω t) _ hU
    (fun ω => (f ω).continuous)
    (fun q => (continuous_eval_const (q : ℝ)).measurable.comp hf)
    (measurable_alternatingExitClock f a hU hV hf ha n)

end LatticeProb
