/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianPathFreezing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRestart
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteStopping

/-!
# Freezing the canonical path at an observed time

The frozen path is measurable in the actual natural filtration. First exit
commutes with freezing up to the freezing time, which supplies a direct
stopping-time criterion for the successive ball exits.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

def frozenBrownianPath {d : ℕ} (t : ℝ≥0) (ω : BrownianPath d) : BrownianPath d :=
  ⟨fun s ↦ ω (min s t), ω.continuous.comp (continuous_id.min continuous_const)⟩

@[simp] lemma frozenBrownianPath_apply {d : ℕ} (t s : ℝ≥0) (ω : BrownianPath d) :
    frozenBrownianPath t ω s = ω (min s t) := rfl

lemma shiftedBrownianPath_frozen {d : ℕ} (ω : BrownianPath d)
    {s t : ℝ≥0} (hst : s ≤ t) :
    shiftedBrownianPath s (frozenBrownianPath t ω) =
      frozenBrownianPath (t - s) (shiftedBrownianPath s ω) := by
  apply ContinuousMap.ext
  intro u
  change ω (min (s + u) t) - ω (min s t) = ω (s + min u (t - s)) - ω s
  rw [min_eq_left hst, add_min, add_tsub_cancel_of_le hst]

lemma measurable_frozenBrownianPath {d : ℕ} (t : ℝ≥0) :
    Measurable[brownianNaturalFiltration d t] (frozenBrownianPath (d := d) t) := by
  apply (@ContinuousMap.measurable_iff_eval ℝ≥0 (Euc d) _ _ _ _ _ _ _ _
    (BrownianPath d) (brownianNaturalFiltration d t) (frozenBrownianPath t)).mpr
  intro s
  exact (comap_measurable (fun ω : BrownianPath d ↦ ω (min s t))).mono
    (le_iSup₂_of_le (min s t) (min_le_right s t) le_rfl) le_rfl

lemma continuousExitTime_le_frozen {d : ℕ} (U : Set (Euc d))
    (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    continuousExitTime U z ω ≤ continuousExitTime U z (frozenBrownianPath t ω) := by
  apply le_iInf
  intro s
  exact (continuousExitTime_le_of_not_mem (ω := ω) (t := min s.val t) s.property).trans
    (ENNReal.coe_le_coe.mpr (min_le_left s.val t))

/-- Freezing preserves an already attained exit and prevents any later exit. -/
theorem continuousExitTime_frozen {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0) :
    continuousExitTime U z (frozenBrownianPath t ω) =
      if continuousExitTime U z ω ≤ (t : ℝ≥0∞) then continuousExitTime U z ω else ∞ := by
  classical
  split_ifs with h
  · apply le_antisymm _ (continuousExitTime_le_frozen U z ω t)
    have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    have htime : (continuousExitTime U z ω).toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
      exact h
    have hout : z + frozenBrownianPath t ω (continuousExitTime U z ω).toNNReal ∉ U := by
      simpa only [frozenBrownianPath_apply, min_eq_left htime] using
        (continuousExitTime_not_mem hU hfinite)
    simpa only [ENNReal.coe_toNNReal hfinite] using continuousExitTime_le_of_not_mem hout
  · apply top_unique
    apply le_iInf
    intro s
    exact False.elim (h ((continuousExitTime_le_of_not_mem (ω := ω) (t := min s.val t) s.property).trans
      (ENNReal.coe_le_coe.mpr (min_le_right s.val t))))

/-- A globally measurable time whose observed events are invariant under
freezing is a stopping time for the canonical natural filtration. -/
theorem isStoppingTime_of_frozen_events {d : ℕ}
    {τ : BrownianPath d → ℝ≥0∞} (hτ : Measurable τ)
    (hfreeze : ∀ t ω, τ (frozenBrownianPath t ω) ≤ (t : ℝ≥0∞) ↔
      τ ω ≤ (t : ℝ≥0∞)) :
    IsStoppingTime (brownianNaturalFiltration d) τ := by
  intro t
  letI : MeasurableSpace (BrownianPath d) := brownianNaturalFiltration d t
  have hm : MeasurableSet {ω | τ (frozenBrownianPath t ω) ≤ (t : ℝ≥0∞)} :=
    measurableSet_le (hτ.comp (measurable_frozenBrownianPath t)) measurable_const
  change MeasurableSet[brownianNaturalFiltration d t] {ω | τ ω ≤ (t : ℝ≥0∞)}
  simpa only [hfreeze] using hm

/-- The whole path observed up to a stopping time is measurable at that time.
On infinite times our existing zero-time totalization is retained explicitly. -/
theorem measurable_frozenBrownianPath_stopping {d : ℕ}
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ) :
    Measurable[hτ.measurableSpace] (fun ω ↦ frozenBrownianPath (τ ω).toNNReal ω) := by
  classical
  apply (@ContinuousMap.measurable_iff_eval ℝ≥0 (Euc d) _ _ _ _ _ _ _ _
    (BrownianPath d) hτ.measurableSpace
    (fun ω ↦ frozenBrownianPath (τ ω).toNNReal ω)).mpr
  intro s
  have hadapt : StronglyAdapted (brownianNaturalFiltration d)
      (fun t (ω : BrownianPath d) ↦ ω (min s t)) := by
    intro t
    exact ((ContinuousMap.measurable_eval s).comp
      (measurable_frozenBrownianPath t)).stronglyMeasurable
  have hprog := hadapt.isStronglyProgressive_of_continuous
    (fun ω ↦ ω.continuous.comp (continuous_const.min continuous_id))
  let f : BrownianPath d → Euc d :=
    stoppedValue (fun t (ω : BrownianPath d) ↦ ω (min s t)) τ
  have hmf : Measurable[hτ.measurableSpace] f := measurable_stoppedValue hprog hτ
  have hm0' : Measurable[brownianNaturalFiltration d 0] (fun ω : BrownianPath d ↦ ω 0) := by
    simpa only [Function.comp_def, frozenBrownianPath_apply, min_self] using
      (ContinuousMap.measurable_eval (0 : ℝ≥0)).comp (measurable_frozenBrownianPath (d := d) 0)
  have hm0 : Measurable[hτ.measurableSpace] (fun ω : BrownianPath d ↦ ω 0) :=
    hm0'.mono (hτ.le_measurableSpace_of_const_le (i := 0) fun _ ↦ bot_le) le_rfl
  have heq : (fun ω ↦ frozenBrownianPath (τ ω).toNNReal ω s) =
      (fun ω ↦ if τ ω = ∞ then ω 0 else f ω) := by
    funext ω
    by_cases h : τ ω = ∞
    · simp [h]
    · rw [if_neg h]
      change ω (min s (τ ω).toNNReal) = ω (min s (τ ω).untopA)
      rw [← ENNReal.coe_toNNReal h]
      rfl
  rw [heq]
  exact hm0.piecewise (hτ.measurable (measurableSet_singleton ∞)) hmf

end BouRabeeGwynne
