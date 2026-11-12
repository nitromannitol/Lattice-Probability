/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.DFGPSM2Asm at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin6
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20Main
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Asm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_10TailMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS arXiv:1905.00380, Lemma 3.19 (T:2264–2300) and Lemma 3.20 (T:2302–2330), from
LM Lemma 3.1 (`LMLem3_1a`, behind Prop 3.1) and the DG results behind Theorem 1.5
(`DGThm1_5KU`, `DGProp3_21`, via `dfgpsScaling_of_lem3_6`).
-/

noncomputable section

namespace LQGMetric.DFGPS
open Blueprint

/-- **DFGPS Lemma 3.19** (`eqn-ep-diam`), constants uniform in the field. -/
theorem lem3_19U (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) : Lem3_19U :=
  L319.lem3_19U_of (prop3_9_of (prop3_1 h31a) (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU hP)))
    (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU hP))

/-- **DFGPS Lemma 3.19** (`eqn-ep-diam-square`), constants uniform in the field. -/
theorem lem3_19SqU (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) : Lem3_19SqU :=
  L319.lem3_19SqU_of
    (prop3_10_of (prop3_1 h31a) (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU hP)))
    (dfgpsScaling_of_lem3_6 h31a (L36.lem3_6_of_DG hKU hP))

/-- **DFGPS Lemma 3.20** (`Blueprint.DFGPSLem3_20`) from the cited results. -/
theorem dfgpsLem3_20_cited (h31a : LMLem3_1a) (hKU : DGThm1_5KU) (hP : DGProp3_21) :
    DFGPSLem3_20 :=
  dfgpsLem3_20_of (lem3_19U h31a hKU hP) (lem3_19SqU h31a hKU hP)

end LQGMetric.DFGPS
