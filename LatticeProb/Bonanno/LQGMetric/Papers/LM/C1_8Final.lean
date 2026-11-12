/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.C1_8Final at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8
import LatticeProb.Bonanno.LQGMetric.Papers.LM.C1_8Lim
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_6Final

/-!
# LM Corollary 1.8 from LM Theorem 1.7 (task P2-LMC18)

Wiring: LM Theorem 1.6 (`LM.lmThm1_6`, proved) and LM Lemma 1.4 (`LM.lmLem1_4`, proved in
`C1_8Lim.lean`) are discharged in `lmCor1_8_of` (`C1_8.lean`; LM l. 323–332). Remaining inputs:
`LMThm1_7` (LM Theorem 1.7, `thm-msrble-general`, l. 306–311, cited) and `CopyAeLength`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric.LM

open Blueprint

/-- **LM Corollary 1.8** (`cor-bilip-msrble`, l. 317–332) from LM Theorem 1.7 and `CopyAeLength` -/
theorem lmCor1_8_of_thm1_7 (h17 : LMThm1_7) (hlen : CopyAeLength) : LMCor1_8 :=
  lmCor1_8_of lmThm1_6 lmLem1_4 h17 hlen

end LQGMetric.LM
