/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianObservedHistory at commit fdb5cad; frozen-history declarations retained; local imports and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianObservedHistory

/-! Actual completed excursions are observable at their exit times. Freezing
supplies this fact for arbitrary measurable history payloads, including flags
and full normalized curves. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

set_option maxHeartbeats 400000 in
theorem measurable_brownianHistory_stopping_of_frozen {d : ℕ}
    {H : Type*} [MeasurableSpace H] {τ : BrownianPath d → ℝ≥0∞}
    (hτ : IsStoppingTime (brownianNaturalFiltration d) τ)
    {history : BrownianPath d → H} (hm : Measurable history)
    (hf : ∀ (t : ℝ≥0) ω, τ ω ≤ (t : ℝ≥0∞) →
      history (frozenBrownianPath t ω) = history ω) :
    Measurable[hτ.measurableSpace] history := by
  have hid : Measurable[⨆ t, brownianNaturalFiltration d t]
      (id : BrownianPath d → BrownianPath d) := by
    apply (@ContinuousMap.measurable_iff_eval ℝ≥0 (Euc d) _ _ _ _ _ _ _ _
      (BrownianPath d) (⨆ t, brownianNaturalFiltration d t) id).mpr
    intro s
    have heval : Measurable[brownianNaturalFiltration d s]
        (fun ω : BrownianPath d ↦ ω s) := by
      simpa only [Function.comp_def, frozenBrownianPath_apply, min_self] using
        (ContinuousMap.measurable_eval s).comp (measurable_frozenBrownianPath (d := d) s)
    exact heval.mono (le_iSup (fun t ↦ brownianNaturalFiltration d t) s) le_rfl
  intro A hA
  refine ⟨(hm.comp hid) hA, ?_⟩
  intro t
  change MeasurableSet[brownianNaturalFiltration d t]
    (history ⁻¹' A ∩ {ω | τ ω ≤ (t : ℝ≥0∞)})
  have heq : history ⁻¹' A ∩ {ω | τ ω ≤ (t : ℝ≥0∞)} =
      (history ∘ frozenBrownianPath t) ⁻¹' A ∩ {ω | τ ω ≤ (t : ℝ≥0∞)} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply]
    constructor <;> rintro ⟨hmem, ht⟩
    · exact ⟨by simpa only [hf t ω ht] using hmem, ht⟩
    · exact ⟨by simpa only [hf t ω ht] using hmem, ht⟩
  rw [heq]
  exact ((hm.comp (measurable_frozenBrownianPath t)) hA).inter (hτ t)

theorem stoppedBrownianRepresentative_frozen_of_exit_le {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0)
    (ht : continuousExitTime U z ω ≤ (t : ℝ≥0∞)) :
    stoppedBrownianRepresentative U z (frozenBrownianPath t ω) =
      stoppedBrownianRepresentative U z ω := by
  have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have htime : (continuousExitTime U z ω).toNNReal ≤ t := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfinite]
    exact ht
  have heq : continuousExitTime U z (frozenBrownianPath t ω) =
      continuousExitTime U z ω := by rw [continuousExitTime_frozen hU, ite_eq_left ht]
  apply ContinuousMap.ext
  intro u
  let q : ℝ≥0 := ⟨(u : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg u.property.1 (continuousExitTime U z ω).toNNReal.property⟩
  have hq : q ≤ t := by
    apply le_trans _ htime
    change (u : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ) ≤
      ((continuousExitTime U z ω).toNNReal : ℝ)
    exact mul_le_of_le_one_left (continuousExitTime U z ω).toNNReal.property u.property.2
  change z + frozenBrownianPath t ω _ = z + ω q
  simp only [heq]
  change z + ω (min q t) = z + ω q
  rw [min_eq_left hq]

theorem stoppedBrownianNextRepresentative_frozen {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d)
    {τ : BrownianPath d → ℝ≥0∞}
    (hτ : ∀ t ω, τ (frozenBrownianPath t ω) =
      if τ ω ≤ (t : ℝ≥0∞) then τ ω else ∞)
    (t : ℝ≥0) (ω : BrownianPath d)
    (ht : brownianNextExitTime U z τ ω ≤ (t : ℝ≥0∞)) :
    stoppedBrownianRepresentative U
      (z + frozenBrownianPath t ω (τ (frozenBrownianPath t ω)).toNNReal)
      (shiftedBrownianPath (τ (frozenBrownianPath t ω)).toNNReal
        (frozenBrownianPath t ω)) =
    stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω) := by
  have hprev := (le_brownianNextExitTime U z τ ω).trans ht
  have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top hprev
  let s : ℝ≥0 := (τ ω).toNNReal
  have hs : τ ω = (s : ℝ≥0∞) := (ENNReal.coe_toNNReal hfinite).symm
  have hst : s ≤ t := ENNReal.coe_le_coe.mp (hs ▸ hprev)
  have hsum : (t : ℝ≥0∞) = (s : ℝ≥0∞) + ((t - s : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hst]
  have hη : continuousExitTime U (z + ω s) (shiftedBrownianPath s ω) ≤
      ((t - s : ℝ≥0) : ℝ≥0∞) := by
    change τ ω + continuousExitTime U (z + ω s) (shiftedBrownianPath s ω) ≤ _ at ht
    rw [hs, hsum, ENNReal.add_le_add_iff_left ENNReal.coe_ne_top] at ht
    exact ht
  rw [hτ t ω, ite_eq_left hprev]
  change stoppedBrownianRepresentative U (z + ω (min s t))
      (shiftedBrownianPath s (frozenBrownianPath t ω)) = _
  rw [min_eq_left hst, shiftedBrownianPath_frozen ω hst]
  exact stoppedBrownianRepresentative_frozen_of_exit_le hU (z + ω s)
    (shiftedBrownianPath s ω) (t - s) hη

end BouRabeeGwynne
