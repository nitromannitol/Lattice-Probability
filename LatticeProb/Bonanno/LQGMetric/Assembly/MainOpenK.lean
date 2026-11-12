/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenK at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenJ
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37Q1

/-!
# Theorems 1.1 and 1.2 from CONF §3 and the DZZ inputs

`theorem11_openJ`/`theorem12_openJ` (Assembly/MainOpenJ.lean) with the cited DG Lemma 3.7
(Ding–Gwynne arXiv:1807.01072, `lem-circle-avg-approx`, on `𝕊(1/2)` by D118) proved:
`DG.L37Q.dgLem3_7` (Papers/DG/S3L37Q1.lean, P2-DGZB: the white-noise zero-boundary GFF of
Ding–Goswami arXiv:1610.09998 realized as a random distribution, with DGo Prop 3.3). The remaining
inputs are `Blueprint.CONFSection3` (Gwynne–Miller arXiv:1905.00381 §3) and `DG.DZZInputsDG`
(Ding–Zeitouni–Zhang arXiv:1807.00422: L5.3 upper half, L6.1 lower half, P3.17 at `μIn` and at the
walls `dgWalls`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **Theorem 1.2** from CONF §3 and the DZZ inputs. -/
theorem theorem12_openK (hC3 : CONFSection3) (hD : DG.DZZInputsDG) : Theorem12 :=
  theorem12_openJ hC3 DG.L37Q.dgLem3_7 hD

/-- **Theorem 1.1** from CONF §3 and the DZZ inputs. -/
theorem theorem11_openK (hC3 : CONFSection3) (hD : DG.DZZInputsDG) : Theorem11 :=
  theorem11_openJ hC3 DG.L37Q.dgLem3_7 hD

end LQGMetric
