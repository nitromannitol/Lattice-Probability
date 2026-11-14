/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianNestedExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNextExit

/-! Nested exits are the direct exits of the original path. The equalities
include infinite exit times and use the actual shifted-path restart map. -/

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

lemma continuousExitTime_mono {d : ℕ} {U V : Set (Euc d)} (hUV : U ⊆ V)
    (z : Euc d) (ω : BrownianPath d) :
    continuousExitTime U z ω ≤ continuousExitTime V z ω := by
  apply le_iInf
  intro t
  exact continuousExitTime_le_of_not_mem (fun hU => t.property (hUV hU))

lemma brownianNextExitTime_eq_of_le {d : ℕ} (V : Set (Euc d)) (z : Euc d)
    (τ : BrownianPath d → ℝ≥0∞) (ω : BrownianPath d)
    (hle : τ ω ≤ continuousExitTime V z ω) :
    brownianNextExitTime V z τ ω = continuousExitTime V z ω := by
  by_cases hfinite : τ ω = ∞
  · have hV : continuousExitTime V z ω = ∞ := top_le_iff.mp (hfinite ▸ hle)
    simp only [brownianNextExitTime, hfinite, top_add, hV]
  · have hcoe : ((τ ω).toNNReal : ℝ≥0∞) = τ ω := ENNReal.coe_toNNReal hfinite
    have htime : ((τ ω).toNNReal : ℝ≥0∞) ≤ continuousExitTime V z ω := by
      simpa only [hcoe] using hle
    have hrestart := continuousExitTime_eq_add_shift V z ω (τ ω).toNNReal htime
    unfold brownianNextExitTime
    simpa only [hcoe] using hrestart.symm

lemma brownianNextExitTime_from_nested_exit {d : ℕ} {U V : Set (Euc d)}
    (hUV : U ⊆ V) (z : Euc d) (ω : BrownianPath d) :
    brownianNextExitTime V z (continuousExitTime U z) ω = continuousExitTime V z ω :=
  brownianNextExitTime_eq_of_le V z (continuousExitTime U z) ω
    (continuousExitTime_mono hUV z ω)

end BouRabeeGwynne
