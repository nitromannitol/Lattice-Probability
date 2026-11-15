import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-! # Measurability of cell walk paths -/

set_option autoImplicit false

open MeasureTheory ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigStepWalk

variable (H : CellConfig) [Countable H.cells]

/-- The cell occupied at a fixed time is measurable in the jump chain. -/
theorem measurable_walk (t : ℝ) :
    Measurable (fun ω : ℕ → H.cells => H.walk ω t) := by
  exact measurable_comp_nat (H.measurable_jumpCount t)
    (fun n => measurable_pi_apply n)

/-- A rescaled step path is measurable for the product σ-algebra on paths. -/
theorem measurable_scaled_walk (p : H.cells → Plane) (ε : ℝ≥0) :
    Measurable (fun ω : ℕ → H.cells => fun t : ℝ≥0 =>
      (ε : ℝ) • p (H.walk ω ((t : ℝ) / (ε : ℝ) ^ 2))) := by
  refine measurable_pi_iff.mpr fun t => ?_
  exact (measurable_const : Measurable (fun _ : ℕ → H.cells => (ε : ℝ))).smul
    ((measurable_of_countable p).comp
    (measurable_walk H ((t : ℝ) / (ε : ℝ) ^ 2)))

end LatticeProb.CellConfigStepWalk
