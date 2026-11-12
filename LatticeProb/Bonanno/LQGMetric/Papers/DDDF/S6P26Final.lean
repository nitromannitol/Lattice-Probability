/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P26Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue3

/-!
# DDDF Prop 26 (5.76), (6.99), (1.3) from the inputs of Theorem 20 (task P2-DDDF6b)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
With the gluing `s6_step1_glue` (Step 1, l. 1289–1294) and (5.75) `s6_eq5_75` (Step 2), DDDF
Prop 26 (5.76) (l. 1262–1329) holds as soon as Theorem 20 does, i.e. from `S6T20Inputs`
(Condition (T) = DDDF Prop 21 and `T20Step4Num`, `T20Step4Den`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

/-- **DDDF Prop 26 (5.76)** (`eq:WeakMul`, l. 1262–1329) from the inputs of Theorem 20. -/
theorem s6_eq5_76_of_T20 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hT : S6T20Inputs ξ W P) : S6Eq5_76 ξ W P :=
  s6_eq5_76_of_glue hW hξ hT (s6_step1_glue ξ)

/-- **DDDF (6.99)** = `Blueprint.DDDFEq6_99` from the inputs of Theorem 20. -/
theorem dddfEq6_99_of_T20
    (hT : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W → S6T20Inputs (xiGamma γ) W P) :
    Blueprint.DDDFEq6_99 :=
  dddfEq6_99_of_glue (fun γ _ _ => s6_step1_glue (xiGamma γ)) hT

/-- **DDDF (1.3)** = `Blueprint.DDDFEq1_3` from the inputs of Theorem 20 and the DG bounds
(5.54), (5.78). -/
theorem dddfEq1_3_of_T20
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
        S6T20Inputs (xiGamma γ) W P ∧
          S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P) :
    Blueprint.DDDFEq1_3 :=
  dddfEq1_3_of_glue (fun γ _ _ => s6_step1_glue (xiGamma γ)) h

end DDDF
end LQGMetric
