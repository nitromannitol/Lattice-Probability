/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsABWire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB5
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6T20Done

/-!
# DDDF (6.102)/(6.103) for `[0,a] × [0,b]` from (5.54) (task P2-DDDF6e, packet O6)

`s6_eq6_102_AB`, `s6_eq6_103_AB` with `Λ_n` bounded from Theorem 20 (`lambda_bdd_of_554`).
DDDF = arXiv:1904.08021, `tightness.tex` l. 1639–1647.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF (6.102)/(6.103)** (l. 1639–1647) for `[0,a] × [0,b]`, `ξ = γ/d_γ`, from (5.54). -/
theorem s6_tails_AB_of_554 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | Real.exp s * lambdaDelta (xiGamma γ) W P δ ≤
          lenObs (xiGamma γ) (phiVer W P δ 1) (rectAB a b) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → δ < 1 →
      P {ω | lenObs (xiGamma γ) (phiVer W P δ 1) (rectAB a b) ω ≤
          Real.exp (-s) * lambdaDelta (xiGamma γ) W P δ} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) :=
  ⟨S6AB.s6_eq6_102_AB hW (xiGamma_pos' hγ) (lambda_bdd_of_554 hγ hγ2 hW h554) ha hb,
    S6AB.s6_eq6_103_AB hW (xiGamma_pos' hγ) (lambda_bdd_of_554 hγ hγ2 hW h554) ha hb⟩

end DDDF
end LQGMetric
