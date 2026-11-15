import LatticeProb.Prob.ContinuousStoppedPath

/-! # Composition of stopped paths -/

set_option autoImplicit false

open scoped ENNReal NNReal

namespace LatticeProb

/-- Stopping a path twice is the same as stopping it at the earlier time. -/
theorem stoppedPath_stoppedPath {E : Type*} [TopologicalSpace E]
    (S T : ℝ≥0∞) (w : C(ℝ≥0, E)) :
    stoppedPath T (stoppedPath S w) = stoppedPath (min S T) w := by
  ext t
  simp only [stoppedPath_apply]
  have hfin : min (t : ℝ≥0∞) T ≠ ⊤ :=
    ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne
  rw [ENNReal.coe_toNNReal hfin]
  rw [min_assoc, min_comm T S]

end LatticeProb
