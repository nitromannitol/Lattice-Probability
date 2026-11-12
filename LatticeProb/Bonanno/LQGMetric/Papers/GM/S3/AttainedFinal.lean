/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedFn
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulusClosed
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip

/-!
# GM Propositions 3.2–3.5: the closed chain (task P2-M2F3)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
§3.2 (l. 1205–1300). Assembly only:

* `gm_P3_2_of_nodes`, `gm_P3_3_of_nodes`: GM Props 3.2, 3.3 (l. 1240, 1245) from the hypotheses of
  `gm_P3_4_of_nodes` (GM Lemma 3.7, Prop 2.2, Lemma 2.11 (closed form) and Blueprint items), with
  GM's footnote at l. 1222 proved (`gm_S3_2fn`).
* `gm_P3_2_bp` … `gm_P3_5_bp`: the same with GM Lemma 3.7 (`gm_L3_7`), Lemma 2.11 (closed form,
  `gm_L2_11_closed`) and Proposition 2.2 (`gm_P2_2`) discharged: only Blueprint items remain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric.GM
open Blueprint

/-- **GM Proposition 3.2** -/
theorem gm_P3_2_of_nodes (h37 : L3_7) (h31a : LMLem3_1a) (h22 : P2_2) (h211 : L2_11c)
    (h38 : DFGPSLem3_8) (h24e : GMS2_4e) (hMQ : MQThm1_2Weak) : P3_2 :=
  gm_P3_2 (gm_P3_4_of_nodes h37 h31a h22 h211 h38 h24e hMQ) gm_S3_2fn

/-- **GM Proposition 3.3** -/
theorem gm_P3_3_of_nodes (h37 : L3_7) (h31a : LMLem3_1a) (h22 : P2_2) (h211 : L2_11c)
    (h38 : DFGPSLem3_8) (h24e : GMS2_4e) (hMQ : MQThm1_2Weak) : P3_3 :=
  gm_P3_3 h22 (gm_P3_2_of_nodes h37 h31a h22 h211 h38 h24e hMQ)

end LQGMetric.GM
