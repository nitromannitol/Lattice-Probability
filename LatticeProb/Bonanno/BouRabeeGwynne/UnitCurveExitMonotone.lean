/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.UnitCurveExitMonotone at commit fdb5cad; local imports adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.UnitCurveExit
import LatticeProb.Bonanno.BouRabeeGwynne.MonotoneStoppedPrefixes

/-! Actual first-exit stopping commutes with continuous monotone clocks
at the level of the genuine Fréchet quotient. -/

open Set
open scoped unitInterval

namespace BouRabeeGwynne

theorem unitCurveExitTime_comp_monotone {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (f : C(unitInterval, Euc d))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1) :
    φ (unitCurveExitTime U (f.comp φ)) = unitCurveExitTime U f := by
  have hsurj : Function.Surjective φ := by
    intro y
    apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval) φ.continuous
    rw [hzero, hone]
    exact ⟨bot_le, le_top⟩
  by_cases hex : ∃ a, f a ∉ U
  · have hexcomp : ∃ a, (f.comp φ) a ∉ U := by
      obtain ⟨b, hb⟩ := hex
      obtain ⟨a, ha⟩ := hsurj b
      exact ⟨a, by simpa only [ContinuousMap.comp_apply, ha] using hb⟩
    apply le_antisymm
    · obtain ⟨a, ha⟩ := hsurj (unitCurveExitTime U f)
      have hout : (f.comp φ) a ∉ U := by
        simpa only [ContinuousMap.comp_apply, ha] using
          unitCurveExitTime_not_mem_of_exists hU hex
      exact (hmono (unitCurveExitTime_le_of_not_mem hout)).trans_eq ha
    · exact unitCurveExitTime_le_of_not_mem
        (unitCurveExitTime_not_mem_of_exists hU hexcomp)
  · have hf : ∀ a, f a ∈ U := by
      simpa only [not_exists, not_not] using hex
    have hg : ∀ a, (f.comp φ) a ∈ U := fun a ↦ hf (φ a)
    rw [unitCurveExitTime_eq_one_of_forall_mem hf,
      unitCurveExitTime_eq_one_of_forall_mem hg, hone]

theorem unitCurveExitProjection_comp_monotone {d : ℕ}
    {U : Set (Euc d)} (hU : IsOpen U) (f : C(unitInterval, Euc d))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (hzero : φ 0 = 0) (hone : φ 1 = 1) :
    unitCurveExitProjection U (f.comp φ) = unitCurveExitProjection U f := by
  unfold unitCurveExitProjection unitCurveExitRepresentative
  exact curveSpace_project_prefix_comp_monotone f φ hmono hzero _ _
    (unitCurveExitTime_comp_monotone hU f φ hmono hzero hone)

end BouRabeeGwynne
