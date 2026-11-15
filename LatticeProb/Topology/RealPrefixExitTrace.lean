import LatticeProb.Prob.PrefixExitClock
import LatticeProb.Topology.RealFirstExitClock
import LatticeProb.Topology.CompactPrefixInterval

/-! # Real-time first-exit prefixes -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- For a finite exit, the infimum of real times whose prefix leaves an open
set equals the forward exit clock. -/
theorem sInf_prefix_exit_eq_openExitTime {E : Type*} [TopologicalSpace E]
    (η : ℝ → E) (U : Set E) (hη : Continuous η) (hU : IsOpen U)
    (hfin : openExitTime (fun s (_ : Unit) => η s) U () ≠ ∞) :
    sInf {t : ℝ | 0 ≤ t ∧ ¬ η '' Icc 0 t ⊆ U} =
      ((openExitTime (fun s (_ : Unit) => η s) U ()).toNNReal : ℝ) := by
  rw [sInf_prefix_exit_eq_sInf_pointwise_exit]
  simpa only [zero_add] using
    sInf_outside_eq_forward_openExitTime η U 0 hη hU (by simpa only [zero_add] using hfin)

/-- A finite stopped prefix of a restricted real-time curve has the same trace
as the original curve on the corresponding real interval. -/
theorem coe_compactPathPrefix_stopped_real {E : Type*} [TopologicalSpace E]
    (η : C(ℝ, E)) (T : ℝ≥0∞) (hT : T ≠ ∞) :
    let w : C(ℝ≥0, E) := ⟨fun t => η t, η.continuous.comp NNReal.continuous_coe⟩
    (compactPathPrefix (stoppedPath T w) T.toNNReal : Set E) =
      η '' Icc (0 : ℝ) (T.toNNReal : ℝ) := by
  dsimp only
  rw [coe_compactPathPrefix_stoppedPath _ T hT]
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, ⟨s.property, hs.2⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs.1⟩, ⟨zero_le, hs.2⟩, rfl⟩

end LatticeProb
