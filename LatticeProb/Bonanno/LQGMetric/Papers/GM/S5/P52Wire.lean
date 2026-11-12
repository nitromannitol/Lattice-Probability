/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.P52Wire at commit fdb5cad; only the module paths of local imports are changed. -/
/-
GM Proposition 5.2 (`P5_2`, l. 2731–2752) with every GM-internal input discharged:
L5.9 (`gm_L5_9`), L5.10 (`gm_L5_10`), L5.8 (`gm_L5_8`), L5.6 (`gm_L5_6_of_geom`), L2.7 (`gm_L2_7`).
-/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.P52Main
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event5LinkRed
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510Final
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes58
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56P4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndep

set_option autoImplicit false

namespace LQGMetric.GM
open Blueprint

/-- **GM Proposition 5.2** from the cited inputs. -/
theorem gm_P5_2 (h38 : DFGPSLem3_8) (h320 : DFGPSLem3_20) (h41 : DFGPSProp4_1)
    (hXi : GMXiQBound) (hLM21 : LMLem2_1) (hMQ : MQLem4_1Gen) : P5_2 :=
  gm_P5_2_of (gm_L5_9 h38)
    (gm_L5_10 (gm_L5_8 (gm_L5_6_of_geom l56GeomN h320 h38) h38 (gm_L2_7 hLM21 hMQ)) h320 h41 hXi)

end LQGMetric.GM
