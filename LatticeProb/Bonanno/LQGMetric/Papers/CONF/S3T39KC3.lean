/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39KC3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39KC2
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorems 1.1 and 1.2 without the CONF Theorem 3.9 leaf (P2-T39FIN)

`theorem11_openQ`/`theorem12_openQ` (Assembly/MainOpenQ.lean) take `CONFW.CONFThm3_9RestAll`.
Here it is discharged by `confThm3_9RestAll_holds` (S3T39KC2, D132 form), with DFGPS
Lemma 3.8 obtained exactly as in Assembly/MainOpenL (`confSection3_openL`) and MainOpenO:
`CONFW.dfgpsLem3_8_of_DG` from `DG.wire_dgThm1_5KU_of`, `DG.wire_dgProp3_21_of` applied to
`DG.dzzInputsDGForm_of (DZZ.dzzInputsDG_of_exp hexp)`.

Remaining input: `DZZ.DZZLem53ExpAll` (or `DZZ.L53HbadBAll`).
-/

noncomputable section

namespace LQGMetric.CONF

open Blueprint

/-- **DFGPS Lemma 3.8** from the DZZ leaf, by the DG chain of `confSection3_openL` -/
theorem dfgpsLem3_8_of_exp (hexp : DZZ.DZZLem53ExpAll) : DFGPSLem3_8 :=
  have hD : DG.DZZInputsDG := DZZ.dzzInputsDG_of_exp hexp
  CONFW.dfgpsLem3_8_of_DG
    (DG.wire_dgThm1_5KU_of DG.L37Q.dgLem3_7 (DG.dgProp3_16_of_lem37 DG.L37Q.dgLem3_7)
      (DG.dzzInputsDGForm_of hD))
    (DG.wire_dgProp3_21_of DG.L37Q.dgLem3_7 (DG.dzzInputsDGForm_of hD))

/-- **the CONF Theorem 3.9 leaf** from the DZZ leaf -/
theorem confThm3_9RestAll_of_exp (hexp : DZZ.DZZLem53ExpAll) : CONFW.CONFThm3_9RestAll :=
  confThm3_9RestAll_holds (dfgpsLem3_8_of_exp hexp)

/-- **Theorem 1.2** with no CONF Theorem 3.9 hypothesis -/
theorem theorem12_openR (hexp : DZZ.DZZLem53ExpAll) : Theorem12 :=
  theorem12_openQ (confThm3_9RestAll_of_exp hexp) hexp

/-- **Theorem 1.1** with no CONF Theorem 3.9 hypothesis -/
theorem theorem11_openR (hexp : DZZ.DZZLem53ExpAll) : Theorem11 :=
  theorem11_openQ (confThm3_9RestAll_of_exp hexp) hexp

/-- **Theorem 1.2** with DZZ L5.3 part 1 reduced to `hbadB` -/
theorem theorem12_openR_hbadB (hb : DZZ.L53HbadBAll) : Theorem12 :=
  theorem12_openR (DZZ.dzzLem53ExpAll_of_hbadB hb)

/-- **Theorem 1.1** with DZZ L5.3 part 1 reduced to `hbadB` -/
theorem theorem11_openR_hbadB (hb : DZZ.L53HbadBAll) : Theorem11 :=
  theorem11_openR (DZZ.dzzLem53ExpAll_of_hbadB hb)

end LQGMetric.CONF
