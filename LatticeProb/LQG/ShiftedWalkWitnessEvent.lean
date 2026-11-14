import LatticeProb.LQG.ShiftedGridContinuousWalk
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Measurable events for shifted-grid walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A curve, mesh, grid shift, interpolation speed, and starting label. -/
abbrev ShiftedWalkParameters := ((C(ℝ, ℂ) × ℝ × ℝ) × ℝ) × ℤ

/-- The spatial representative at the starting label. -/
def shiftedWalkStart (p : ShiftedWalkParameters) : ℂ :=
  shiftedGridAnchor p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2

/-- The interpolated walk associated with a shifted grid. -/
def shiftedWalkPath (p : ShiftedWalkParameters) (ξ : ℕ → ℤ) : C(ℝ≥0, ℂ) :=
  ConstantStepInterpolation.continuousPath p.1.2
    (fun n => shiftedGridAnchor p.1.1.1 p.1.1.2.1 p.1.1.2.2 (ξ n))

/-- The starting representative depends measurably on the parameters. -/
theorem measurable_shiftedWalkStart : Measurable shiftedWalkStart := by
  have h : Measurable (fun p : ShiftedWalkParameters =>
      (p.1.1, p.2)) := measurable_fst.fst.prodMk measurable_snd
  have h' : Measurable (fun q : (C(ℝ, ℂ) × ℝ × ℝ) × ℤ =>
      shiftedGridAnchor q.1.1 q.1.2.1 q.1.2.2 q.2) :=
    measurable_from_prod_countable_left fun k => (continuous_shiftedGridAnchor k).measurable
  exact h'.comp h

/-- The interpolated path depends measurably on both parameters and walk. -/
theorem measurable_shiftedWalkPath :
    Measurable (fun q : ShiftedWalkParameters × (ℕ → ℤ) => shiftedWalkPath q.1 q.2) := by
  apply ConstantStepInterpolation.measurable_continuousPath_of
  · have h : Measurable (fun q : ShiftedWalkParameters × (ℕ → ℤ) =>
        (q.1.1.1, q.2)) := measurable_fst.fst.fst.prodMk measurable_snd
    exact measurable_shiftedGridWalkAnchors.comp h
  · exact measurable_fst.fst.snd


/-- The quenched probability of a fixed Borel path event is measurable in the
parameters when the walk law is an s-finite measurable kernel. -/
theorem measurable_shiftedWalk_event_probability
    (κ : Kernel ShiftedWalkParameters (ℕ → ℤ)) [IsSFiniteKernel κ]
    {U : Set C(ℝ≥0, ℂ)} (hU : MeasurableSet U) :
    Measurable (fun p => κ p {ξ | shiftedWalkPath p ξ ∈ U}) := by
  exact Kernel.measurable_kernel_prodMk_left (hU.preimage measurable_shiftedWalkPath)

/-- Starting labels in a Borel region whose event probability is below a fixed
threshold form a Borel witness relation. -/
theorem measurableSet_shiftedWalk_witness
    (κ : Kernel ShiftedWalkParameters (ℕ → ℤ)) [IsSFiniteKernel κ]
    {U : Set C(ℝ≥0, ℂ)} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞) :
    MeasurableSet {p : ShiftedWalkParameters | shiftedWalkStart p ∈ K ∧
      κ p {ξ | shiftedWalkPath p ξ ∈ U} ≤ t} :=
  (hK.preimage measurable_shiftedWalkStart).inter
    (measurableSet_le (measurable_shiftedWalk_event_probability κ hU) measurable_const)

end LatticeProb
