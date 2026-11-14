/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianExitRestart at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianWeakMarkov

/-!
# Deterministic restart of the actual continuous exit

The identities here concern each continuous path. They connect the genuine
first-exit map to the Brownian shift used in the proved Markov property.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma continuousExitTime_pos_of_mem {d : ℕ} {U : Set (Euc d)} (hU : IsOpen U)
    {z : Euc d} {ω : BrownianPath d} (hstart : z + ω 0 ∈ U) :
    0 < continuousExitTime U z ω := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hfinite : continuousExitTime U z ω ≠ ∞ := by simp [hzero]
  have hout := continuousExitTime_not_mem hU hfinite
  exact hout (by simpa [hzero] using hstart)

/-- Restarting at a time before the first exit removes precisely that elapsed
time. This includes the infinite-exit case and uses no probabilistic premise. -/
theorem continuousExitTime_eq_add_shift {d : ℕ} (U : Set (Euc d))
    (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime U z ω) :
    continuousExitTime U z ω = (t : ℝ≥0∞) +
      continuousExitTime U (z + ω t) (shiftedBrownianPath t ω) := by
  have hpath (s : ℝ≥0) :
      (z + ω t) + shiftedBrownianPath t ω s = z + ω (t + s) := by
    change (z + ω t) + (ω (t + s) - ω t) = z + ω (t + s)
    abel
  apply le_antisymm
  · change continuousExitTime U z ω ≤ (t : ℝ≥0∞) + ⨅ s :
      {s : ℝ≥0 // (z + ω t) + shiftedBrownianPath t ω s ∉ U}, (s.val : ℝ≥0∞)
    rw [ENNReal.add_iInf]
    apply le_iInf
    intro s
    have hout : z + ω (t + s.val) ∉ U := by simpa only [hpath] using s.property
    simpa only [ENNReal.coe_add] using continuousExitTime_le_of_not_mem hout
  · apply le_iInf
    intro s
    have hts : t ≤ s.val :=
      ENNReal.coe_le_coe.mp (ht.trans (continuousExitTime_le_of_not_mem s.property))
    have hout : (z + ω t) + shiftedBrownianPath t ω (s.val - t) ∉ U := by
      simpa only [hpath, add_tsub_cancel_of_le hts] using s.property
    calc
      _ ≤ (t : ℝ≥0∞) + ((s.val - t : ℝ≥0) : ℝ≥0∞) :=
        add_le_add_right (continuousExitTime_le_of_not_mem hout) _
      _ = (s.val : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, add_tsub_cancel_of_le hts]

/-- The restarted actual exit has exactly the same spatial endpoint. -/
theorem continuousExitTime_shift_endpoint {d : ℕ} (U : Set (Euc d))
    (z : Euc d) (ω : BrownianPath d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ continuousExitTime U z ω)
    (hfinite : continuousExitTime U z ω ≠ ∞) :
    (z + ω t) + shiftedBrownianPath t ω
      (continuousExitTime U (z + ω t) (shiftedBrownianPath t ω)).toNNReal =
      z + ω (continuousExitTime U z ω).toNNReal := by
  have heq := continuousExitTime_eq_add_shift U z ω t ht
  have hshift : continuousExitTime U (z + ω t) (shiftedBrownianPath t ω) ≠ ∞ := by
    intro htop
    exact hfinite (by simpa only [htop, add_top] using heq)
  have htime : (continuousExitTime U z ω).toNNReal = t +
      (continuousExitTime U (z + ω t) (shiftedBrownianPath t ω)).toNNReal := by
    simpa only [ENNReal.toNNReal_add ENNReal.coe_ne_top hshift, ENNReal.toNNReal_coe]
      using congrArg ENNReal.toNNReal heq
  rw [htime]
  change (z + ω t) + (ω (t +
      (continuousExitTime U (z + ω t) (shiftedBrownianPath t ω)).toNNReal) - ω t) =
    z + ω (t + (continuousExitTime U (z + ω t) (shiftedBrownianPath t ω)).toNNReal)
  abel

end BouRabeeGwynne
