import LatticeProb.Prob.AlternatingSegmentAvoidance
import LatticeProb.Prob.AlternatingClockEndpoints

/-! # Alternating segments outside nested open sets -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Before the excursion count, each exit clock starts outside the inner set. -/
theorem alternatingExitClock_not_mem_of_lt {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V) (hUV : U ⊆ V)
    (ω : Ω) (hstart : f ω ((a ω).untopD 0) ∉ U) (n : ℕ)
    (hn : n < alternatingExcursionCount f a U V ω) :
    f ω ((alternatingExitClock f a U V n ω).untopD 0) ∉ U := by
  cases n with
  | zero => exact hstart
  | succ n =>
      have hfin := (alternatingSegmentEndpoints_of_lt f a U V ω (n + 1) hn).1
      have hout : f ω ((alternatingExitClock f a U V (n + 1) ω).untopD 0) ∉ V :=
        closedExitAfter_not_mem f _ hV ω hfin
      exact fun hu => hout (hUV hu)

/-- Before the excursion count, each closed exit-to-entry segment avoids the inner set. -/
theorem alternatingSegment_image_subset_compl_of_initial {Ω : Type*} {d : ℕ}
    (f : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))) (a : Ω → WithTop ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (ω : Ω) (hstart : f ω ((a ω).untopD 0) ∉ U) (n : ℕ)
    (hn : n < alternatingExcursionCount f a U V ω) :
    f ω '' Icc ((alternatingExitClock f a U V n ω).untopD 0)
      ((openEntryAfter (fun ω t => f ω t) (alternatingExitClock f a U V n) U ω).untopD 0) ⊆ Uᶜ :=
  alternatingSegment_image_subset_compl f a hU ω n hn
    (alternatingExitClock_not_mem_of_lt f a hV hUV ω hstart n hn)

end LatticeProb
