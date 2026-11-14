/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.CrossingTimesCoupling
import LatticeProb.Prob.MarkovPathKernelStrictStopping

/-!
# The inverse crossing clock is a strict stopping time

For `x ∈ C(ℝ≥0, E)` the crossing clock `u ↦ crossClock m x u` at time `q` depends only on the path
stopped at `q` (`crossClock_stopped`), hence is measurable for the filtration of stopped paths
(`measurable_crossClock_stoppedPath`).  Consequently, for every `t`,
`{A_t < u} ∈ ℱ_u` where `A_t = pathClockInv m x t` is the inverse crossing clock
(`measurableSet_pathClockInv_lt`): `A_t` is an optional time, and the strong Markov property
for strict stopping times applies to it.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The crossing clock of a continuous path at time `u` only depends on the path stopped at `u`. -/
theorem crossClock_stopped (m : ℝ≥0∞) (x : C(ℝ≥0, E)) (u : ℝ≥0) :
    crossClock m (fun s => x (min s u)) u = crossClock m (fun s => x s) u := by
  unfold crossClock
  congr 1
  funext n
  have h := crossCount_stopped (f := fun s => x s) x.continuous
    (ε := (2 : ℝ)⁻¹ ^ n) (by positivity) u
  rw [h]

/-- The crossing clock at time `q ≤ u` is measurable for the filtration of stopped paths at `u`. -/
theorem measurable_crossClock_stoppedPath (m : ℝ≥0∞) {q u : ℝ≥0} (hq : q ≤ u) :
    Measurable[stoppedPathFiltration (E := E) u] fun x : C(ℝ≥0, E) =>
      crossClock m (fun s => x s) q := by
  have hg : Measurable fun y : C(ℝ≥0, E) => crossClock m (fun s => y s) q :=
    measurable_crossClock m q
  have hcomp : (fun x : C(ℝ≥0, E) => crossClock m (fun s => x s) q) =
      (fun y : C(ℝ≥0, E) => crossClock m (fun s => y s) q) ∘
        fun x : C(ℝ≥0, E) => stopPath x q := by
    funext x
    exact (crossClock_stopped m x q).symm
  have hs : Measurable[stoppedPathFiltration (E := E) q] fun x : C(ℝ≥0, E) => stopPath x q :=
    comap_measurable (fun x : C(ℝ≥0, E) => stopPath x q)
  rw [hcomp]
  exact (hg.comp hs).mono ((stoppedPathFiltration (E := E)).mono hq) le_rfl

/-- **The inverse crossing clock is a strict stopping time of the filtration of stopped paths**:
`{A_t < u}` is determined by the path stopped at `u`. -/
theorem measurableSet_pathClockInv_lt (m : ℝ≥0∞) (t u : ℝ≥0) :
    MeasurableSet[stoppedPathFiltration (E := E) u]
      {x : C(ℝ≥0, E) | pathClockInv m x t < (u : ℝ≥0∞)} := by
  have hset : {x : C(ℝ≥0, E) | pathClockInv m x t < (u : ℝ≥0∞)} =
      ⋃ r : ℚ, {x : C(ℝ≥0, E) | ((ratTime r : ℝ≥0) : ℝ≥0∞) < u ∧
        (t : ℝ≥0∞) ≤ crossClock m (fun s => x s) (ratTime r)} := by
    ext x
    simp only [pathClockInv, clockInv, iInf_lt_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u', hu', hu'u⟩
      have hlt : (u' : ℝ) < (u : ℝ) := by exact_mod_cast hu'u
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
      refine ⟨r, ?_, ?_⟩
      · rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, ratTime_coe_of_lt hr1]
        exact hr2
      · exact hu'.trans (crossClock_mono m _ (le_ratTime_of_lt hr1))
    · rintro ⟨r, hr, hc⟩
      exact ⟨ratTime r, hc, hr⟩
  rw [hset]
  refine MeasurableSet.iUnion fun r => ?_
  by_cases h : ((ratTime r : ℝ≥0) : ℝ≥0∞) < u
  · simp only [h, true_and]
    exact measurableSet_le measurable_const
      (measurable_crossClock_stoppedPath m (ENNReal.coe_le_coe.1 h.le))
  · simp [h]

/-- **Strong Markov property at the inverse crossing clock `A_t`**, shifted-path form: for a
continuous family of laws `K` with the Markov property at deterministic times from `z`, and `A_t`
almost surely finite. -/
theorem strongMarkov_pathClockInv {K : E → ProbabilityMeasure C(ℝ≥0, E)} (hK : Continuous K)
    {z : E} (hM : ∀ t, MarkovAt K z t) (m : ℝ≥0∞) (t : ℝ≥0)
    (hfin : ∀ᵐ x ∂(K z : Measure C(ℝ≥0, E)), pathClockInv m x t < ⊤)
    {g : C(ℝ≥0, E) × C(ℝ≥0, E) → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ p, ‖g p‖ ≤ C) :
    ∫ x, g (stopPath x (pathClockInv m x t).toNNReal, pathShift x (pathClockInv m x t).toNNReal)
        ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, ∫ w, g (stopPath x (pathClockInv m x t).toNNReal, w)
        ∂(K (x (pathClockInv m x t).toNNReal) : Measure C(ℝ≥0, E))
        ∂(K z : Measure C(ℝ≥0, E)) :=
  strongMarkov_of_strictStopping hK hM (σ := fun x => pathClockInv m x t)
    (measurableSet_pathClockInv_lt m t) hfin hg hC

end LatticeProb
