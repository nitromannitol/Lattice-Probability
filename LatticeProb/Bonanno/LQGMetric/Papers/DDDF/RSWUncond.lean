/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWUncond at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Main
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C8High

/-!
# DDDF RSW estimates, unconditionally (task P2-DDDF16, step 0)

The RSW results `rsw_high`, `rsw_low_unif`, `rsw_high_unif`, `rsw_low_quantile`,
`rsw_high_quantile` (DDDF Prop 7 = Prop 14, `tightness.tex` l. 653–662, 783–810) and
`psi_rsw_low_quantile`, `psi_rsw_high_quantile` (DDDF Cor 8, l. 664–676) were proved under the
hypothesis `Prop10 ξ P W`; `prop10` (P10Main.lean) proves it for `ξ > 0`. Pure wiring.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF Corollary 8, (3.38)** (small quantiles for `ψ`), unconditional. -/
theorem psi_rsw_low_quantile' (hW : IsWhiteNoise P W) (hξ : 0 < ξ) (Q : PsiParams)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) :=
  psi_rsw_low_quantile hW Q (prop10 hW hξ) hA hAB

/-- **DDDF Corollary 8, (3.39)** (high quantiles for `ψ`), unconditional. -/
theorem psi_rsw_high_quantile' (hW : IsWhiteNoise P W) (hξ : 0 < ξ) (Q : PsiParams)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) :=
  psi_rsw_high_quantile hW hξ.le Q (prop10 hW hξ) hA hAB

end DDDF
end LQGMetric
