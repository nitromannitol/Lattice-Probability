/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.PhysicalPrefixExit at commit fdb5cad; local import paths are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianPhysicalSegments

/-! First-exit stopping of a genuine physical-time prefix recovers the
original normalized stopped path whenever the prefix reaches its exit. -/

open Set
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

lemma unitCurveExitTime_eq_of_exit_at {d : ℕ} {U : Set (Euc d)}
    (hU : IsOpen U) (f : C(unitInterval, Euc d)) (b : unitInterval)
    (hout : f b ∉ U) (hbefore : ∀ a < b, f a ∈ U) : unitCurveExitTime U f = b := by
  apply le_antisymm (unitCurveExitTime_le_of_not_mem hout)
  by_contra h
  exact (unitCurveExitTime_not_mem_of_exists hU ⟨b, hout⟩)
    (hbefore _ (lt_of_not_ge h))

lemma physicalTimeSegment_initial_apply {d : ℕ} (z : Euc d) (ω : BrownianPath d)
    (T : ℝ≥0) (a : unitInterval) :
    physicalTimeSegment z ω 0 T a =
      z + ω ⟨(a : ℝ) * T, mul_nonneg a.property.1 T.property⟩ := by
  simp only [physicalTimeSegment, ContinuousMap.coe_mk, NNReal.coe_zero, mul_zero, zero_add]

lemma prefix_physicalTimeSegment_eq {d : ℕ} (z : Euc d) (ω : BrownianPath d)
    (T S : ℝ≥0) (b : unitInterval) (hb : (b : ℝ) * T = S) :
    prefixUnitCurve (physicalTimeSegment z ω 0 T) b = physicalTimeSegment z ω 0 S := by
  apply ContinuousMap.ext
  intro u
  change physicalTimeSegment z ω 0 T (b * u) = physicalTimeSegment z ω 0 S u
  rw [physicalTimeSegment_initial_apply, physicalTimeSegment_initial_apply]
  apply congrArg (fun t : ℝ≥0 ↦ z + ω t)
  apply Subtype.ext
  change ((b : ℝ) * (u : ℝ)) * T = (u : ℝ) * S
  rw [← hb]
  ring

theorem unitCurveExitTime_physicalTimeSegment_mul {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d)
    (T : ℝ≥0) (hτ : continuousExitTime U z ω ≤ (T : ℝ≥0∞)) :
    (unitCurveExitTime U (physicalTimeSegment z ω 0 T) : ℝ) * T =
      (continuousExitTime U z ω).toNNReal := by
  have hfinite : continuousExitTime U z ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
  have hτNN : (continuousExitTime U z ω).toNNReal ≤ T := by
    simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono ENNReal.coe_ne_top hτ
  by_cases hT : T = 0
  · subst T
    have ht0 : (continuousExitTime U z ω).toNNReal = 0 := le_antisymm hτNN (bot_le)
    simp only [NNReal.coe_zero, mul_zero, ht0]
  · have hTpos : 0 < (T : ℝ) := lt_of_le_of_ne T.property (by
      intro h
      exact hT (Subtype.ext h.symm))
    let b : unitInterval := ⟨((continuousExitTime U z ω).toNNReal : ℝ) / T,
      div_nonneg (continuousExitTime U z ω).toNNReal.property hTpos.le,
      (div_le_one hTpos).mpr hτNN⟩
    have hb : (b : ℝ) * T = (continuousExitTime U z ω).toNNReal :=
      div_mul_cancel₀ _ hTpos.ne'
    have hout : physicalTimeSegment z ω 0 T b ∉ U := by
      rw [physicalTimeSegment_initial_apply]
      have ht : (⟨(b : ℝ) * T, mul_nonneg b.property.1 T.property⟩ : ℝ≥0) =
          (continuousExitTime U z ω).toNNReal := Subtype.ext hb
      rw [ht]
      exact continuousExitTime_not_mem hU hfinite
    have hbefore : ∀ a < b, physicalTimeSegment z ω 0 T a ∈ U := by
      intro a hab
      rw [physicalTimeSegment_initial_apply]
      apply mem_of_lt_continuousExitTime
      rw [← ENNReal.coe_toNNReal hfinite]
      apply ENNReal.coe_lt_coe.mpr
      exact (lt_div_iff₀ hTpos).mp hab
    have heq := unitCurveExitTime_eq_of_exit_at hU (physicalTimeSegment z ω 0 T) b hout hbefore
    rw [heq]
    exact hb

theorem unitCurveExitRepresentative_physicalTimeSegment {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d)
    (T : ℝ≥0) (hτ : continuousExitTime U z ω ≤ (T : ℝ≥0∞)) :
    unitCurveExitRepresentative U (physicalTimeSegment z ω 0 T) =
      stoppedBrownianRepresentative U z ω := by
  unfold unitCurveExitRepresentative
  rw [prefix_physicalTimeSegment_eq z ω T _ _
    (unitCurveExitTime_physicalTimeSegment_mul hU z ω T hτ)]
  exact (stoppedBrownianRepresentative_eq_physicalTimeSegment U z ω).symm

theorem unitCurveExitProjection_physicalTimeSegment {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (z : Euc d) (ω : BrownianPath d)
    (T : ℝ≥0) (hτ : continuousExitTime U z ω ≤ (T : ℝ≥0∞)) :
    unitCurveExitProjection U (physicalTimeSegment z ω 0 T) =
      stoppedBrownianCurve U z ω := by
  unfold unitCurveExitProjection stoppedBrownianCurve
  rw [unitCurveExitRepresentative_physicalTimeSegment hU z ω T hτ]

end BouRabeeGwynne
