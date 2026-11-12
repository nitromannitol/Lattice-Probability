/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenL at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenK
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3Sec3W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5InputsW1

/-!
# Theorems 1.1 and 1.2 from the remaining CONF and DZZ leaves (task P2-CONFW)

`theorem11_openK`/`theorem12_openK` (Assembly/MainOpenK.lean) with both hypotheses wired down:
* `DG.DZZInputsDG` by `DZZInW.dzzInputsDG_of_leaves` (Papers/DZZ/S5InputsW1.lean) from
  - `DZZLem53EventAll`: the event leaf of DZZ Lemma 5.3 at the walled tilde boxes;
  - `DZZProp317WallsAll`: the walled DZZ Prop 3.17 at the walls `dgWalls` (DZZ Remark 5.2);
  - `DZZChiIdent`: the exponent of DZZ L5.3 at `μIn` is a positive DZZ Thm 1.1 exponent
    (DZZ Prop 5.1, l. 2254–2258), so that it is `chiDZZ γ`;
* `Blueprint.CONFSection3` by `CONFW.confSection3_of_leaves` (Papers/CONF/S3Sec3W1.lean) from
  - `CONF.CONFLem2_10AtConfU`: CONF Lemma 2.10 at the domains `confU` (DEC-127);
  - `CONFW.CONFThm3_9RestAll`: the remaining CONF Theorem 3.9 node (DEC-120 §5);
  - `DGThm1_5KU`, `DGProp3_21`, obtained here from `DG.DZZInputsDG` and the proved DG L3.7, P3.16.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **`CONFSection3` from the remaining CONF leaves and the DZZ inputs** -/
theorem confSection3_openL (hL : CONF.CONFLem2_10AtConfU) (hRest : CONFW.CONFThm3_9RestAll)
    (hD : DG.DZZInputsDG) : CONFSection3 :=
  CONFW.confSection3_of_leaves hL hRest
    (DG.wire_dgThm1_5KU_of DG.L37Q.dgLem3_7 (DG.dgProp3_16_of_lem37 DG.L37Q.dgLem3_7)
      (DG.dzzInputsDGForm_of hD))
    (DG.wire_dgProp3_21_of DG.L37Q.dgLem3_7 (DG.dzzInputsDGForm_of hD))

end LQGMetric
