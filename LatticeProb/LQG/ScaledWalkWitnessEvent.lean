import LatticeProb.LQG.ShiftedWalkWitnessEvent

/-! # Scaled witness events for shifted-grid walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The environment parameters of a shifted-grid walk, excluding its start. -/
abbrev ShiftedWalkEnvironment := (C(ℝ, ℂ) × ℝ × ℝ) × ℝ

/-- Environment, spatial scale, and starting integer, ordered for witness events. -/
abbrev ScaledWalkWitness := ShiftedWalkEnvironment × (ℝ × ℤ)

/-- Recover the walk parameters from an environment and a starting integer. -/
def scaledWalkParameters (q : ScaledWalkWitness) : ShiftedWalkParameters :=
  (q.1, q.2.2)

/-- Recovery of the walk parameters is measurable. -/
theorem measurable_scaledWalkParameters : Measurable scaledWalkParameters :=
  measurable_fst.prodMk measurable_snd.snd

/-- The physical starting representative at the given spatial scale. -/
def scaledWalkStart (q : ScaledWalkWitness) : ℂ :=
  q.2.1 • shiftedWalkStart (scaledWalkParameters q)

/-- The scaled starting representative is measurable jointly in all parameters. -/
theorem measurable_scaledWalkStart : Measurable scaledWalkStart := by
  exact measurable_snd.fst.smul
    (measurable_shiftedWalkStart.comp measurable_scaledWalkParameters)

/-- The interpolated walk indexed by a scaled witness. -/
def scaledWalkPath (q : ScaledWalkWitness) (ξ : ℕ → ℤ) : C(ℝ≥0, ℂ) :=
  shiftedWalkPath (scaledWalkParameters q) ξ

set_option maxHeartbeats 400000 in
/-- The walk path is jointly measurable with the witness and trajectory. -/
theorem measurable_scaledWalkPath :
    Measurable (fun z : ScaledWalkWitness × (ℕ → ℤ) => scaledWalkPath z.1 z.2) := by
  have hp : Measurable (fun z : ScaledWalkWitness × (ℕ → ℤ) =>
      (scaledWalkParameters z.1, z.2)) :=
    (measurable_scaledWalkParameters.comp measurable_fst).prodMk measurable_snd
  simpa only [scaledWalkPath, Function.comp_def] using (measurable_shiftedWalkPath.comp hp)

/-- The probability of a jointly measurable path event is measurable. -/
theorem measurable_scaledWalk_event_probability
    (κ : Kernel ScaledWalkWitness (ℕ → ℤ)) [IsSFiniteKernel κ]
    {U : Set (ScaledWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U) :
    Measurable (fun q : ScaledWalkWitness =>
      κ q {ξ | (q, scaledWalkPath q ξ) ∈ U}) := by
  exact κ.measurable_kernel_prodMk_left
    (hU.preimage (measurable_fst.prodMk measurable_scaledWalkPath))

/-- The scaled starting-anchor constraint and a quenched probability bound
form a measurable witness relation. -/
theorem measurableSet_scaledWalk_witness
    (κ : Kernel ScaledWalkWitness (ℕ → ℤ)) [IsSFiniteKernel κ]
    {U : Set (ScaledWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞) :
    MeasurableSet {q : ScaledWalkWitness | scaledWalkStart q ∈ K ∧
      κ q {ξ | (q, scaledWalkPath q ξ) ∈ U} ≤ t} :=
  (hK.preimage measurable_scaledWalkStart).inter
    (measurableSet_le (measurable_scaledWalk_event_probability κ hU) measurable_const)

end LatticeProb
