/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenG at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainReducedS
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_7A
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.T1_4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412mMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412nMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412kBridge
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412U4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L217R
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12Blueprint
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Inc3
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V20
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGKer
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412pMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412oRK
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq2Fin

/-!
# Theorems 1.1 and 1.2 with the DDDF inputs reduced (status 2026-10-02 17:10)

`theorem11_openF`/`theorem12_openF` (Assembly/MainOpenF.lean) with DDDF Theorem 1 replaced by its
proof: DDDF Thm 1(1) from (5.54), (5.78) (from the DG leaves via `DDDF.S6DG.s6Eq5_54_of_DG`,
`s6Eq5_78_of_DG` and the proved Ding–Goswami kernel bounds) and the two Step-1 statements of DDDF
Prop 28 for the δ-family (`DDDFStep1Leaves`, DDDF-internal, open); DDDF Thm 1(2) only on (−1,2)²,
proved inside `DFGPS.Q12.dfgps_existence_reduced_554` from Thm 1(1), DDDF Prop 29 on the square
(`DDDF.P29WN.dddfProp29Sq`) and (5.54). The remaining hypotheses: the cited DG results, the CONF §3
package, and `DDDFStep1Leaves`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint MeasureTheory WhiteNoise

/-- the DDDF-internal open nodes: DDDF Prop 28 Step 1 (both parts) for the δ-family
(DDDF tightness.tex T:1414–1436, T:1455–1472, 1648) -/
def DDDFStep1Leaves : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ), WhiteNoise.IsWhiteNoise P W →
    (∀ β : ℝ, 0 < β → β < xiGamma γ * (Q γ - 2) → DDDF.S6P28.S6UpperStep1 (xiGamma γ) W P β) ∧
    (∀ α : ℝ, xiGamma γ * (Q γ + 2) < α → DDDF.S6P28.S6LowerStep1 (xiGamma γ) W P α)

/-- DDDF (5.54) from the DG leaves -/
theorem dddf554_of_DG (hKU : DGThm1_5KU) : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), WhiteNoise.IsWhiteNoise P W →
    DDDF.S6Eq5_54 (xiGamma γ) (Q γ) W P :=
  fun _ hγ hγ2 _ _ _ _ hW => DDDF.S6DG.s6Eq5_54_of_DG hKU
    (DDDF.S6DG.wpPhiCompare_of_kerBounds DDDF.S6DGKer.freeKerBounds) hγ hγ2 hW

/-- **DDDF Theorem 1 (1)** from the DG leaves and the DDDF Prop 28 Step-1 nodes -/
theorem dddfThm1_1_of_leaves (hKU : DGThm1_5KU) (hP3 : DGProp3_21) (hS : DDDFStep1Leaves) :
    DDDFThm1_1 :=
  DDDF.S6P28.dddfThm1_1_of_step1 fun γ hγ hγ2 _ _ P W hW =>
    ⟨dddf554_of_DG hKU γ hγ hγ2 P W hW,
      DDDF.S6DG.s6Eq5_78_of_DG hP3
        (DDDF.S6DG.wpPhiCompare_of_kerBounds DDDF.S6DGKer.freeKerBounds) hγ hγ2 hW,
      (hS γ hγ hγ2 P W hW).1, (hS γ hγ hγ2 P W hW).2⟩

/-- **Theorem 1.2** (status 17:10): from the cited DG results, the CONF §3 package and the
DDDF-internal nodes `DDDFStep1Leaves`. -/
theorem theorem12_openG (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU) (hP321 : DGProp3_21)
    (hC3 : CONFSection3) (hSt : DDDFStep1Leaves) : Theorem12 :=
  have hS : DFGPSScaling :=
    DFGPS.dfgpsScaling_of_lem3_6 LM.lmLem3_1a (DFGPS.L36.lem3_6_of_DG hKU hP321)
  have h38 : DFGPSLem3_8 := DFGPS.dfgpsLem3_8_of hS LM.lmLem3_1a
  have hC27 : CONFLem2_7 := CONF.confLem2_7 h38
  have hC14 : CONFThm1_4 := CONF.confThm1_4 h38 hC3
  theorem12_of_blueprint
    (gm_weak_uniqueness_reducedS (GM.gm_P4_12S h38 hC27 hC14 hC3
      (GM.p412n_P412OfL36AE0' GM.p412o_confRKAddConst)) hDG hKU hP321 hC27 hC14)
    (DFGPS.Q12.dfgps_existence_reduced_554 (dddfThm1_1_of_leaves hKU hP321 hSt)
      (dddf554_of_DG hKU) (DDDF.S6DGKer.dddfEq1_3_of_DG' hKU hP321)
      (DDDF.S6DGKer.dddfEq6_99_of_DG' hKU) DDDF.P29WN.dddfProp29Sq LM.lmCor1_8) hS

/-- **Theorem 1.1** (status 17:10). -/
theorem theorem11_openG (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU) (hP321 : DGProp3_21)
    (hC3 : CONFSection3) (hSt : DDDFStep1Leaves) : Theorem11 :=
  GM.theorem11_of_theorem12 (theorem12_openG hDG hKU hP321 hC3 hSt)

end LQGMetric
