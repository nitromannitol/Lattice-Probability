/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenJ at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenI
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P16D3

/-!
# Theorems 1.1 and 1.2 without the DG Prop 3.16 hypothesis (D126)

`theorem11_openI`/`theorem12_openI` (Assembly/MainOpenI.lean) with the cited DG Proposition 3.16
(Ding–Gwynne arXiv:1807.01072, `prop-lfpp-approx`, in the corrected form of decision D126 —
the printed statement is false, `DG.not_dgProp3_16Printed`) proved from DG Lemma 3.7
(`DG.dgProp3_16_of_lem37`, Papers/DG/S3P16D3.lean, P2-DG126). The remaining inputs are
`Blueprint.CONFSection3`, `Blueprint.DGLem3_7` and `DG.DZZInputsDG`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **Theorem 1.2** from CONF §3, DG L3.7 and the DZZ inputs. -/
theorem theorem12_openJ (hC3 : CONFSection3) (h37 : DGLem3_7) (hD : DG.DZZInputsDG) :
    Theorem12 :=
  theorem12_openI hC3 h37 (DG.dgProp3_16_of_lem37 h37) hD

/-- **Theorem 1.1** from CONF §3, DG L3.7 and the DZZ inputs. -/
theorem theorem11_openJ (hC3 : CONFSection3) (h37 : DGLem3_7) (hD : DG.DZZInputsDG) :
    Theorem11 :=
  theorem11_openI hC3 h37 (DG.dgProp3_16_of_lem37 h37) hD

end LQGMetric
