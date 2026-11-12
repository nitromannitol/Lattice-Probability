/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510Final at commit fdb5cad; only the module paths of local imports are changed. -/
/-
GM Lemma 5.10 (`L5_10`, l. 3307–3335) from its parts: conditions (5), (6), (9), (10)
(P2-M2M6, L510C*.lean) and the deterministic-tube Lemma 5.8 (D92).
-/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C8
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C6
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C3
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C2

set_option autoImplicit false

namespace LQGMetric.GM
open Blueprint

/-- **GM Lemma 5.10** from GM Lemma 5.8, DFGPS Lemma 3.20, DFGPS Prop 4.1 and GM's bound on ξ Q. -/
theorem gm_L5_10 (h58 : L5_8) (h320 : DFGPSLem3_20) (h41 : DFGPSProp4_1) (hXi : GMXiQBound) :
    L5_10 :=
  gm_L5_10_of_parts h58 (gm_L510Diam h320) (gm_L510Bdy h41 hXi) (gm_L510Line h320) gm_L510Dir

end LQGMetric.GM
