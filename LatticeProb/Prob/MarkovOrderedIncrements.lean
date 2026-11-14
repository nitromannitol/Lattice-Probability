import LatticeProb.Prob.MarkovCumulativeProduct

/-!
# Successive increments of ordered observation times

A nondecreasing list of observation times is recovered by taking cumulative
sums of its successive nonnegative increments.
-/

set_option autoImplicit false

open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- Replace observation times by increments measured from the preceding time. -/
def orderedTimeIncrements (t : ℝ≥0) :
    List (ℝ≥0 × (E →ᵇ ℝ)) → List (ℝ≥0 × (E →ᵇ ℝ))
  | [] => []
  | (s, f) :: rest => (s - t, f) :: orderedTimeIncrements s rest

/-- Cumulative sums recover a nondecreasing list of observation times. -/
theorem cumulativeTests_orderedTimeIncrements (t : ℝ≥0)
    (tests : List (ℝ≥0 × (E →ᵇ ℝ)))
    (ht : ∀ p ∈ tests, t ≤ p.1)
    (hs : tests.Pairwise (fun p q => p.1 ≤ q.1)) :
    cumulativeTests t (orderedTimeIncrements t tests) = tests := by
  induction tests generalizing t with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨s, f⟩
    have hts : t ≤ s := ht _ (List.mem_cons_self ..)
    have hrest : ∀ p ∈ rest, s ≤ p.1 := (List.pairwise_cons.mp hs).1
    have hsum : t + (s - t) = s := add_tsub_cancel_of_le hts
    simp only [orderedTimeIncrements, cumulativeTests, hsum]
    rw [ih s hrest (List.pairwise_cons.mp hs).2]

end LatticeProb
