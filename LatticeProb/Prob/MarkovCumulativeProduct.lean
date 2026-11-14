import LatticeProb.Prob.MarkovProductTests

/-!
# Product tests at cumulative times

An ordered product test evaluates its factors at successive cumulative times.
-/

set_option autoImplicit false

open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- The absolute observation times obtained from successive time increments. -/
def cumulativeTests (t : ℝ≥0) : List (ℝ≥0 × (E →ᵇ ℝ)) → List (ℝ≥0 × (E →ᵇ ℝ))
  | [] => []
  | (s, f) :: rest => (t + s, f) :: cumulativeTests (t + s) rest

/-- A shifted ordered test is the product of the tests at their cumulative times. -/
theorem orderedProductTest_pathShift_eq_prod (tests : List (ℝ≥0 × (E →ᵇ ℝ)))
    (t : ℝ≥0) (x : C(ℝ≥0, E)) :
    orderedProductTest tests (pathShift x t) =
      ((cumulativeTests t tests).map fun p => p.2 (x p.1)).prod := by
  induction tests generalizing t with
  | nil => simp [orderedProductTest, cumulativeTests]
  | cons p rest ih =>
    rcases p with ⟨s, f⟩
    have hshift : pathShift (pathShift x t) s = pathShift x (t + s) := by
      ext u
      simp only [pathShift_apply, add_assoc]
    change f ((pathShift x t) s) * orderedProductTest rest (pathShift (pathShift x t) s) =
      f (x (t + s)) * ((cumulativeTests (t + s) rest).map fun p => p.2 (x p.1)).prod
    rw [pathShift_apply, hshift, ih]

end LatticeProb
