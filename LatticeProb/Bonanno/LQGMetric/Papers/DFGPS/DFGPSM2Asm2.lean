/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.DFGPSM2Asm2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.DFGPSM2Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_21Proof3
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_22Main
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_18

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemmas 3.21, 3.22 and Proposition 3.18 from the cited results only

DFGPS arXiv:1905.00380, Lemma 3.21 (T:2337–2357), Lemma 3.22 and Proposition 3.18, from
LM Lemma 3.1 (`LMLem3_1a`, behind Prop 3.1) and the DG results behind Theorem 1.5
(`DGThm1_5KU`, `DGProp3_21`, via `dfgpsScaling_of_lem3_6`), as `dfgpsLem3_20_cited`.
-/

noncomputable section

namespace LQGMetric.DFGPS
open Blueprint

/-- **DFGPS Lemma 3.21** (`eqn-ep-cross`), constants uniform in the field. -/
theorem lem3_21U (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) : Lem3_21U :=
  L321.lem3_21U_of (prop3_1 h31a) (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU hP))

/-- **DFGPS Proposition 3.18** (`Blueprint.DFGPSProp3_18`) from the cited results. -/
theorem dfgpsProp3_18_cited (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) :
    DFGPSProp3_18 :=
  dfgpsProp3_18_of (lem3_19U h31a hKU hP) (lem3_21U h31a hKU hP)

end LQGMetric.DFGPS
