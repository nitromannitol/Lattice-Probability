/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenQ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenO
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127Leaf

/-!
# Theorems 1.1 and 1.2 from the two remaining leaves (`DZZLem53ExpAll` form)

`theorem11_openO`/`theorem12_openO` (Assembly/MainOpenO.lean, P2-DZZ53W) with CONF Lemma 2.10 at
the domains `confU` (Gwynne–Miller arXiv:1905.00381, C:712–742; decision D127) discharged by
`CONF.ZBM.confLem2_10AtConfU_holds` (Papers/CONF/S3D127Leaf.lean). The remaining inputs are
`CONFW.CONFThm3_9RestAll` (the rest of CONF Thm 3.9, D130/D130B/D132) and `DZZ.DZZLem53ExpAll`
(the exponent of DZZ arXiv:1807.00422 Lemma 5.3 exists at `μIn`, D131), which is implied by the
earlier leaf `DZZInW.DZZLem53EventAll` (`DZZ.dzzLem53ExpAll_of_eventAll`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **Theorem 1.2** from the two remaining leaves. -/
theorem theorem12_openQ (hRest : CONFW.CONFThm3_9RestAll) (hexp : DZZ.DZZLem53ExpAll) :
    Theorem12 :=
  theorem12_openO CONF.ZBM.confLem2_10AtConfU_holds hRest hexp

/-- **Theorem 1.1** from the two remaining leaves. -/
theorem theorem11_openQ (hRest : CONFW.CONFThm3_9RestAll) (hexp : DZZ.DZZLem53ExpAll) :
    Theorem11 :=
  theorem11_openO CONF.ZBM.confLem2_10AtConfU_holds hRest hexp

end LQGMetric
