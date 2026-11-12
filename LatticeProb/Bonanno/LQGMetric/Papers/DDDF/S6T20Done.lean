/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6T20Done at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EMain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Final

/-!
# DDDF Theorem 20 inputs from (5.54) alone (task P2-DDDF6d)

`S6T20Inputs (xiGamma γ) W P` (S6Wire) from the DG bound (5.54) only: Condition (T) is DDDF
Prop 21 (`S6.s6_conditionT_psiQ₁`, `tightness.tex` l. 972–1018), (5.67) is `dddf_t20_step4_den`,
and the circuit gluing (5.65)–(5.66) (l. 1097–1123) is `dddf_t20_circuit_glue` for the parameters
`psiQ₁` (`ε₀ = 1/4 ≤ 1`). The downstream results of S6Wire / S6Eq698Main / S6P21Wire are restated
with the Theorem 20 inputs discharged: (6.98) (l. 1608–1613), (5.76) and (5.77) (Prop 26,
l. 1262–1329, via `s6_eq5_76_of_T20` of S6P26Final), `Blueprint.DDDFEq6_99` from (5.54) alone
(l. 1615–1638), `Blueprint.DDDFEq1_3` from (5.54) and (5.78) (l. 162–166), and (6.102)/(6.103)
for `[0,1]²` (l. 1641–1647).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **The inputs of DDDF Theorem 20** for `ξ = γ/d_γ` from (5.54) alone. -/
theorem s6T20Inputs_of_554 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) : S6T20Inputs (xiGamma γ) W P :=
  s6T20Inputs_of_glue hγ hγ2 hW h554
    (dddf_t20_circuit_glue hW S6.psiQ₁ (by norm_num [S6.psiQ₁]))

/-- `Λ_∞(φ, p) < ∞` (DDDF Theorem 20) for `ξ = γ/d_γ` from (5.54). -/
theorem lambda_bdd_of_554 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN (xiGamma γ) W P n (ENNReal.ofReal p) ≤ B :=
  lambda_bdd_of_T20 hW (xiGamma_pos' hγ) (s6T20Inputs_of_554 hγ hγ2 hW h554)

/-- **DDDF (6.98)** for `ξ = γ/d_γ` from (5.54). -/
theorem s6_eq6_98_of_554 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) : S6Eq6_98 (xiGamma γ) W P := by
  obtain ⟨Q, hQ, hε, hT, hN, hD⟩ := s6T20Inputs_of_554 hγ hγ2 hW h554
  exact s6_eq6_98 hW Q hQ hε (xiGamma_pos' hγ) hT hN hD

/-- **DDDF (5.76)** (Prop 26, `s6_eq5_76_of_T20`) for `ξ = γ/d_γ` from (5.54). -/
theorem s6_eq5_76_of_554 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) : S6Eq5_76 (xiGamma γ) W P :=
  s6_eq5_76_of_T20 hW (xiGamma_pos' hγ) (s6T20Inputs_of_554 hγ hγ2 hW h554)

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from (5.54). -/
theorem dddfEq6_99_of_554
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W → S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_T20 fun γ hγ hγ2 _ _ P W hW =>
    s6T20Inputs_of_554 hγ hγ2 hW (h γ hγ hγ2 P W hW)

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from the DG bounds (5.54), (5.78). -/
theorem dddfEq1_3_of_554
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_T20 fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨h54, h78⟩ := h γ hγ hγ2 P W hW
    exact ⟨s6T20Inputs_of_554 hγ hγ2 hW h54, h54, h78⟩

end DDDF
end LQGMetric
