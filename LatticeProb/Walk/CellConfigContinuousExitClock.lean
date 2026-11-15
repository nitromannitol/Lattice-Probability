import LatticeProb.Walk.CellConfigExitClockCurve
import LatticeProb.Prob.OpenExitTimeReparam

/-! # Continuous exit curves under changes of walk clock -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb

/-- Continuous exit curves agree under an increasing change of clock when the
first exit is finite. -/
theorem normalized_exit_curve_eq_of_orderIso {d : ℕ}
    (f g : BrownianPath d) (φ : ℝ≥0 ≃o ℝ≥0)
    (h : ∀ t, f t = g (φ t)) {U : Set (Euc d)} (hU : IsOpen U)
    (hf : continuousExitTime U 0 f ≠ ∞) :
    continuousExitTime U 0 g ≠ ∞ ∧
    normalizedPrefixCurve f (continuousExitTime U 0 f).toNNReal =
      normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal := by
  have hout : g (φ (continuousExitTime U 0 f).toNNReal) ∉ U := by
    simpa only [zero_add, h] using continuousExitTime_not_mem hU hf
  have hg : continuousExitTime U 0 g ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (continuousExitTime_le_of_not_mem (by simpa only [zero_add] using hout))
  have he (a : BrownianPath d) : continuousExitTime U 0 a =
      openExitTime (fun t (_ : Unit) => a t) U () := by
    change (⨅ t : {t : ℝ≥0 // 0 + a t ∉ U}, (t.val : ℝ≥0∞)) =
      ⨅ t : {t : ℝ≥0 // a t ∉ U}, (t.val : ℝ≥0∞)
    apply le_antisymm <;> apply le_iInf <;> intro t
    · exact iInf_le_of_le ⟨t.val, by simpa only [zero_add] using t.property⟩ le_rfl
    · exact iInf_le_of_le ⟨t.val, by simpa only [zero_add] using t.property⟩ le_rfl
  have ht := openExitTime_comp_orderIso_toNNReal g U φ hU g.continuous (by
    rw [← he]; exact hg)
  have htime : (continuousExitTime U 0 f).toNNReal =
      φ.symm (continuousExitTime U 0 g).toNNReal := by
    rw [he f, he g]
    simpa only [← h] using ht
  refine ⟨hg, ?_⟩
  rw [htime, normalizedPrefixCurve_eq_of_orderIso f g φ h, φ.apply_symm_apply]

namespace CellConfigInterpolation

/-- The constant-step continuous-exit curve is close to its first-exterior-vertex
curve, with error controlled by the two cells on the final edge. -/
theorem edist_constantStep_exit_curve_le (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε m : ℝ≥0} (hε : 0 < ε) (hm : 0 < m) {U : Set Plane}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ,
      hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      let g := ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n))
      continuousExitTime U 0 g ≠ ∞ ∧
      edist (normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal)
        (normalizedPrefixCurve g (ConstantStepInterpolation.knot m (n + 1))) ≤
        ENNReal.ofReal (2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)))) := by
  obtain ⟨n, hn, hf, hd⟩ :=
    edist_exit_curve_constantStep_le H hH p hp ω hpos hunb hadj hε hm hU hconv hstart hfin
  obtain ⟨φ, _, heq⟩ :=
    exists_orderIso_interpolatedWalk_eq_constantStep H p ω hpos hunb hε hm
  obtain ⟨hg, hc⟩ := normalized_exit_curve_eq_of_orderIso
    (H.interpolatedWalk p ε ω)
    (ConstantStepInterpolation.continuousPlanePath m (fun n => (ε : ℝ) • p (ω n)))
    φ heq hU hf
  exact ⟨n, hn, hg, hc ▸ hd⟩

end CellConfigInterpolation
end LatticeProb
end
