/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianObservedHistory at commit fdb5cad; only endpoint identities are retained. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNextExit

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma stoppedBrownianRepresentative_endPoint {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (ω : BrownianPath d) :
    stoppedBrownianRepresentative U z ω 1 = z + ω (continuousExitTime U z ω).toNNReal :=
  stoppedBrownianCurve_endPoint

theorem stoppedBrownianRepresentative_next_endPoint {d : ℕ}
    (U : Set (Euc d)) (z : Euc d) (τ : BrownianPath d → ℝ≥0∞) (ω : BrownianPath d)
    (hfinite : brownianNextExitTime U z τ ω ≠ ∞) :
    stoppedBrownianRepresentative U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω) 1 =
        z + ω (brownianNextExitTime U z τ ω).toNNReal := by
  have hparts := ENNReal.add_ne_top.mp hfinite
  rw [stoppedBrownianRepresentative_endPoint]
  simp only [brownianNextExitTime, ENNReal.toNNReal_add hparts.1 hparts.2]
  change z + ω (τ ω).toNNReal +
    (ω ((τ ω).toNNReal + (continuousExitTime U (z + ω (τ ω).toNNReal)
      (shiftedBrownianPath (τ ω).toNNReal ω)).toNNReal) - ω (τ ω).toNNReal) = _
  abel

end BouRabeeGwynne
