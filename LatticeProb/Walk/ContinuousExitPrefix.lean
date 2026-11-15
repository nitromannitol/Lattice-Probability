import LatticeProb.Walk.CellConfigContinuousExitClock

/-! # Continuous first-exit curves under prefix agreement -/

set_option autoImplicit false
noncomputable section

open Set BouRabeeGwynne
open scoped NNReal ENNReal

namespace LatticeProb

/-- Agreement through an exterior time preserves both first exit and its curve. -/
theorem continuousExitTime_and_curve_eq_of_prefix {d : ℕ}
    (f g : BrownianPath d) {U : Set (Euc d)} (hU : IsOpen U) (T : ℝ≥0)
    (hfg : ∀ t ≤ T, f t = g t) (hout : f T ∉ U) :
    continuousExitTime U 0 f ≠ ∞ ∧
      continuousExitTime U 0 g = continuousExitTime U 0 f ∧
      normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal =
        normalizedPrefixCurve f (continuousExitTime U 0 f).toNNReal := by
  have hfT : continuousExitTime U 0 f ≤ (T : ℝ≥0∞) :=
    continuousExitTime_le_of_not_mem (by simpa only [zero_add] using hout)
  have hf : continuousExitTime U 0 f ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hfT
  have hfbound : (continuousExitTime U 0 f).toNNReal ≤ T :=
    (ENNReal.toNNReal_le_toNNReal hf ENNReal.coe_ne_top).2 hfT
  have hfout : f (continuousExitTime U 0 f).toNNReal ∉ U := by
    simpa only [zero_add] using continuousExitTime_not_mem hU hf
  have hg_le : continuousExitTime U 0 g ≤ continuousExitTime U 0 f := by
    rw [← ENNReal.coe_toNNReal hf]
    apply continuousExitTime_le_of_not_mem
    simpa only [zero_add, ← hfg _ hfbound] using hfout
  have hg : continuousExitTime U 0 g ≠ ∞ := ne_top_of_le_ne_top hf hg_le
  have hgbound : (continuousExitTime U 0 g).toNNReal ≤ T :=
    ((ENNReal.toNNReal_le_toNNReal hg hf).2 hg_le).trans hfbound
  have hgout : g (continuousExitTime U 0 g).toNNReal ∉ U := by
    simpa only [zero_add] using continuousExitTime_not_mem hU hg
  have hf_le : continuousExitTime U 0 f ≤ continuousExitTime U 0 g := by
    rw [← ENNReal.coe_toNNReal hg]
    apply continuousExitTime_le_of_not_mem
    simpa only [zero_add, hfg _ hgbound] using hgout
  have heq := le_antisymm hg_le hf_le
  refine ⟨hf, heq, ?_⟩
  rw [heq]
  apply edist_eq_zero.mp
  refine le_antisymm ((normalizedPrefixCurve_edist_le_stopped_ray_cost_all g f _ _
    (OrderIso.refl ℝ≥0)).trans ?_) bot_le
  apply iSup_le
  intro t
  simp only [OrderIso.refl_apply]
  rw [← hfg _ ((min_le_right _ _).trans hfbound), edist_self]

end LatticeProb
end
