import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import Mathlib.Topology.Semicontinuity.Basic

/-! # Lower semicontinuity of ball exit times -/

set_option autoImplicit false

open Filter Set
open scoped ENNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

variable {d : ℕ}

/-- The first exit time is jointly lower semicontinuous in the path and radius. -/
theorem lowerSemicontinuous_ballClock :
    LowerSemicontinuous (fun p : Path d × ℝ => ballClock p.1 p.2) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a = ⊤
  · subst a
    simp only [Set.preimage, Set.mem_Iic, le_top, Set.ofPred_true]
    exact isClosed_univ
  · rw [← ENNReal.coe_toNNReal ha]
    exact isClosed_ballClock_le a.toNNReal

/-- Strict lower bounds on a limiting exit time hold eventually along any convergent filter. -/
theorem eventually_lt_ballClock {α : Type*} {l : Filter α} {F : α → Path d × ℝ}
    {p : Path d × ℝ} (hF : Tendsto F l (𝓝 p)) {a : ℝ≥0∞}
    (ha : a < ballClock p.1 p.2) :
    ∀ᶠ i in l, a < ballClock (F i).1 (F i).2 :=
  hF.eventually ((lowerSemicontinuous_ballClock p) a ha)

end LatticeProb.UnboundedRayIntervalIntegrand
