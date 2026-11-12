/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenI at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenH
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3Wire3

/-!
# Theorems 1.1 and 1.2 with the DG chain wired (task P2-DGWIRE)

`theorem11_openH`/`theorem12_openH` (Assembly/MainOpenH.lean) with `DG.DGThm1_5`,
`Blueprint.DGThm1_5KU` and `Blueprint.DGProp3_21` proved (`DG.wire_dgThm1_5_of`,
`DG.wire_dgThm1_5KU_of`, `DG.wire_dgProp3_21_of`, Papers/DG/S3Wire3.lean) from the cited
DG Lemma 3.7 and DG Proposition 3.16 (Ding–Gwynne arXiv:1807.01072) and the DZZ-level inputs
`DG.DZZInputsDG` (Ding–Zeitouni–Zhang arXiv:1807.00422: L5.3 upper half, L6.1 lower half,
Prop 3.17 at `μIn` and at the walled measures).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **Theorem 1.2** from CONF §3, DG L3.7, DG P3.16 and the DZZ inputs. -/
theorem theorem12_openI (hC3 : CONFSection3) (h37 : DGLem3_7) (h316 : DGProp3_16)
    (hD : DG.DZZInputsDG) : Theorem12 :=
  have hD' : DG.DZZInputsDGForm := DG.dzzInputsDGForm_of hD
  theorem12_openH (DG.wire_dgThm1_5_of h37 h316 hD') (DG.wire_dgThm1_5KU_of h37 h316 hD')
    (DG.wire_dgProp3_21_of h37 hD') hC3

/-- **Theorem 1.1** from CONF §3, DG L3.7, DG P3.16 and the DZZ inputs. -/
theorem theorem11_openI (hC3 : CONFSection3) (h37 : DGLem3_7) (h316 : DGProp3_16)
    (hD : DG.DZZInputsDG) : Theorem11 :=
  have hD' : DG.DZZInputsDGForm := DG.dzzInputsDGForm_of hD
  theorem11_openH (DG.wire_dgThm1_5_of h37 h316 hD') (DG.wire_dgThm1_5KU_of h37 h316 hD')
    (DG.wire_dgProp3_21_of h37 hD') hC3

end LQGMetric
