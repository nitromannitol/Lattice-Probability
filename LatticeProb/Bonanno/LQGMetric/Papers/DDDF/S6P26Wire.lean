/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Wire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Sub
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Mul
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Wire

/-!
# DDDF Prop 26 (5.76), (6.99), (1.3) from the Step-1 circuit bound (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
(5.75) is proved (`s6_eq5_75`), so (5.76) (Prop 26, l. 1262–1329) needs only the pathwise circuit
bound of Step 1 (`S6Step1Circ`), itself reduced to the deterministic gluing `S6Step1Glue`
(`s6Step1Circ_of_glue`), and the inputs of Theorem 20 (`S6T20Inputs`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- **DDDF (5.76)** (Prop 26) from the Step-1 circuit bound and the inputs of Theorem 20. -/
theorem s6_eq5_76_of_circ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hT : S6T20Inputs ξ W P) (hC : S6Step1Circ ξ W P) : S6Eq5_76 ξ W P :=
  s6_eq5_76 hW hξ hT (s6_eq5_75 hW hξ) (s6_eq5_76_up hW hξ (lambda_bdd_of_T20 hW hξ hT)
    (by obtain ⟨Q, hQ, hε, hT', hN, hD⟩ := hT; exact s6_eq6_98 hW Q hQ hε hξ hT' hN hD) hC)

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from the Step-1 circuit bound and the inputs of
Theorem 20. -/
theorem dddfEq6_99_of_circ
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Step1Circ (xiGamma γ) W P ∧ S6T20Inputs (xiGamma γ) W P) :
    Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_576 fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨hC, hT⟩ := h γ hγ hγ2 P W hW
    exact ⟨s6_eq5_76_of_circ hW (xiGamma_pos' hγ) hT hC, hT⟩

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from the Step-1 circuit bound, the inputs of
Theorem 20 and the DG bounds (5.54), (5.78). -/
theorem dddfEq1_3_of_circ
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6Step1Circ (xiGamma γ) W P ∧ S6T20Inputs (xiGamma γ) W P ∧
          S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_576 fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨hC, hT, h54, h78⟩ := h γ hγ hγ2 P W hW
    exact ⟨s6_eq5_76_of_circ hW (xiGamma_pos' hγ) hT hC, hT, h54, h78⟩

/-- **DDDF (5.76)** from the deterministic gluing of Step 1 and the inputs of Theorem 20. -/
theorem s6_eq5_76_of_glue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hT : S6T20Inputs ξ W P) (hG : S6Step1Glue ξ) : S6Eq5_76 ξ W P :=
  s6_eq5_76_of_circ hW hξ hT (s6Step1Circ_of_glue hW hξ hG)

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from the deterministic gluing of Step 1 and the
inputs of Theorem 20. -/
theorem dddfEq6_99_of_glue (hG : ∀ γ : ℝ, 0 < γ → γ < 2 → S6Step1Glue (xiGamma γ))
    (hT : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W → S6T20Inputs (xiGamma γ) W P) :
    Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_circ fun γ hγ hγ2 Ω _ P W hW =>
    ⟨s6Step1Circ_of_glue hW (xiGamma_pos' hγ) (hG γ hγ hγ2), hT γ hγ hγ2 P W hW⟩

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from the deterministic gluing of Step 1, the inputs of
Theorem 20 and the DG bounds (5.54), (5.78). -/
theorem dddfEq1_3_of_glue (hG : ∀ γ : ℝ, 0 < γ → γ < 2 → S6Step1Glue (xiGamma γ))
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6T20Inputs (xiGamma γ) W P ∧
          S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_circ fun γ hγ hγ2 Ω _ P W hW => by
    obtain ⟨hT, h54, h78⟩ := h γ hγ hγ2 P W hW
    exact ⟨s6Step1Circ_of_glue hW (xiGamma_pos' hγ) (hG γ hγ hγ2), hT, h54, h78⟩

end DDDF
end LQGMetric
