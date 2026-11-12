/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Wire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Expo
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Low

/-!
# DDDF (6.99) and (1.3) from (5.76) and the hypotheses of Theorem 20 (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
Wiring of `s6_eq6_98` (DDDF (6.98), l. 1608–1613) into `dddfEq6_99_of_s6` and
`dddfEq1_3_of_s6`. Remaining inputs: (5.76) (`S6Eq5_76`, DDDF Prop 26), Condition (T)
(DDDF Prop 21), `T20Step4Num`, `T20Step4Den` (DDDF Theorem 20, Step 4) and, for (1.3), the DG
bounds (5.54), (5.78).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

lemma xiGamma_pos' {γ : ℝ} (hγ : 0 < γ) : 0 < xiGamma γ := by
  have hχ : 0 < chiDZZ γ := by
    unfold chiDZZ; split_ifs with h
    · exact h.choose_spec.1
    · norm_num
  exact div_pos hγ (div_pos two_pos hχ)

/-- the inputs of DDDF Theorem 20 for `ξ` (Condition (T) = DDDF Prop 21, Step 4 = (5.65)–(5.67)) -/
def S6T20Inputs {Ω : Type*} [MeasurableSpace Ω] (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) :
    Prop :=
  ∃ Q : PsiParams, PsiSmall Q ∧ Q.ε₀ < 1 / 2 ∧ ConditionT ξ Q W P ∧ T20Step4Num ξ Q W P ∧
    T20Step4Den ξ Q W P

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from (5.76) and the inputs of Theorem 20. -/
theorem dddfEq6_99_of_576
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Eq5_76 (xiGamma γ) W P ∧ S6T20Inputs (xiGamma γ) W P) :
    Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_s6 fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨h76, Q, hQ, hε, hT, hN, hD⟩ := h γ hγ hγ2 P W hW
    exact ⟨h76, s6_eq6_98 hW Q hQ hε (xiGamma_pos' hγ) hT hN hD⟩

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from (5.76), the inputs of Theorem 20 and the DG
bounds (5.54), (5.78). -/
theorem dddfEq1_3_of_576
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Eq5_76 (xiGamma γ) W P ∧ S6T20Inputs (xiGamma γ) W P ∧
          S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_s6 fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨h76, ⟨Q, hQ, hε, hT, hN, hD⟩, h54, h78⟩ := h γ hγ hγ2 P W hW
    exact ⟨h76, s6_eq6_98 hW Q hQ hε (xiGamma_pos' hγ) hT hN hD, h54, h78⟩

/-- `Λ_∞(φ, p) < ∞` for small `p` from the inputs of Theorem 20 (`dddf_thm20_of_num_den`) -/
theorem lambda_bdd_of_T20 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    {ξ : ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) (h : S6T20Inputs ξ W P) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B := by
  obtain ⟨Q, hQ, hε, hT, hN, hD⟩ := h
  obtain ⟨p₀, hp₀, h'⟩ := dddf_thm20_of_num_den hW Q hQ hε hξ hT hN hD
  exact ⟨p₀, hp₀, fun p hp hpp => (h' p hp hpp).1⟩

/-- **DDDF (5.76)** from the pathwise (5.75), the upper half (Prop 26 Step 1) and the inputs of
Theorem 20 -/
theorem s6_eq5_76 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    {ξ : ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ) (hT : S6T20Inputs ξ W P)
    (h75 : S6Eq5_75 ξ W P) (hUp : S6Eq5_76Up ξ W P) : S6Eq5_76 ξ W P :=
  s6Eq5_76_of_halves hW (s6_eq5_76_low hW hξ (lambda_bdd_of_T20 hW hξ hT) h75) hUp

end DDDF
end LQGMetric
