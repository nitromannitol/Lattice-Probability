/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainReducedS at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.M1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Thm19
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.Prop61Rest
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43cFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.P52Wire
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes55
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedSwap
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulusClosed
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate6Main
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.BilipR
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.SphereMain
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightBlueprint
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_8
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1Main
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_3FMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFGPSM2Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFGPSM2Asm2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L217R
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12Blueprint
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412S
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Final
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.L2_4S2

/-!
# M2 and Theorems 1.1/1.2 from GM Proposition 4.12 at the CONF §3 parameters (D104, P2-M2J2i)

Primed copies of `gm_weak_uniqueness_reduced` (Assembly/M2Reduced.lean), `theorem12_reduced`,
`theorem11_reduced` (Assembly/MainReduced.lean) with `GM.GMP4_12S` (Papers/GM/S4/P412S.lean) in
place of `GM.GMP4_12` (GM Theorem 4.2 from `GM.gm_T4_2S`), and LM Lemma 3.1(a) discharged by
`LM.lmLem3_1a` (Papers/LM/L3_4M6.lean) and LM Theorem 1.6 by `LM.lmThm1_6`
(Papers/LM/T1_6Final.lean), CONF Lemma 2.4 by `CONF.confLem2_4` (Papers/CONF/L2_4S2.lean).
Wiring only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **GM Theorem 1.9** (`Blueprint.GMWeakUniqueness`) from GM Proposition 4.12 at the CONF §3
parameters and the still-open cited inputs. -/
theorem gm_weak_uniqueness_reducedS (hP412 : GM.GMP4_12S)
    (hDG : DG.DGThm1_5) (hKU : DGThm1_5KU) (hP321 : DGProp3_21)
    (hC27 : CONFLem2_7) (hC14 : CONFThm1_4) :
    GMWeakUniqueness := by
  have h31a : LMLem3_1a := LM.lmLem3_1a
  have hLM16 : LMThm1_6 := LM.lmThm1_6
  have hLM21 : LMLem2_1 := MarkovFinal.lmLem2_1
  have hMQG : MQLem4_1Gen := MQ.mqLem4_1Gen
  have hS : DFGPSScaling := DFGPS.dfgpsScaling_of_lem3_6 h31a (DFGPS.L36.lem3_6_of_DG hKU hP321)
  have h38 : DFGPSLem3_8 := DFGPS.dfgpsLem3_8_of hS h31a
  have hMQ : MQThm1_2Weak := MQ.mqThm1_2Weak h38
  have hC24 : CONFLem2_4 := CONF.confLem2_4 h38
  have h318 : DFGPSProp3_18 := DFGPS.dfgpsProp3_18_cited h31a hKU hP321
  have h320 : DFGPSLem3_20 := DFGPS.dfgpsLem3_20_cited h31a hKU hP321
  have h41 : DFGPSProp4_1 := DFGPS.P41.dfgpsProp4_1_of_DG h31a hDG hKU hP321
  have h43 : DFGPSProp4_3F := DFGPS.dfgpsProp4_3F_of h31a hS
  have h24a : GMS2_4a := GM.Tight.blueprint_GMS2_4a
  have h24c : GMS2_4c := GM.Tight.blueprint_GMS2_4c
  have h24e : GMS2_4e := GM.Tight.blueprint_GMS2_4e_of hS h31a
  have hXi : GMXiQBound := DG.gmXiQBound_of_dgThm1_5' hDG
  have hT : GM.T4_2 :=
    GM.gm_T4_2S h31a h24e h318 h320 h38 hC24 hC27 hC14 h43 hMQ hP412
  have h22 : GM.P2_2 := GM.Bilip.gm_P2_2' hLM16 h24a h24c
  have h211 : GM.L2_11c := GM.gm_L2_11_closed h41 hXi
  have hP43 : GM.P4_3 := GM.gm_P4_3 h22
    (GM.gm_P3_5 h22 (GM.gm_P3_4_of_nodes (GM.gm_L3_7 h38) h31a h22 h211 h38 h24e hMQ))
    (GM.gm_L5_5 h211) (GM.gm_P5_2 h38 h320 h41 hXi hLM21 hMQG) h38
  exact GM.gm_T1_9 (GM.gm_L3_1 (GM.gm_L2_7 hLM21 hMQG) h22 h38)
    (GM.gm_P3_2_of_nodes (GM.gm_L3_7 h38) h31a h22 h211 h38 h24e hMQ)
    (GM.gm_P3_3_of_nodes (GM.gm_L3_7 h38) h31a h22 h211 h38 h24e hMQ)
    (GM.gm_P6_1 hT hP43 hMQ h318 h24e h24c h22)
    (GM.gm_S6_23 h22)

end LQGMetric
