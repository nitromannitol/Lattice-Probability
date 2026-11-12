/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate5Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4Enlarge
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate4PairRed

/-!
# GM Theorem 4.2 from its one-pair form (DEC-89, packets D, E, F; D95)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Thm 4.2 (l. 1554–1571) and the end of
its proof (l. 2437–2446). The chain `T4_2PairOne → T4_2Pair → T4_2Gt1S → T4_2Gt1E (= T4_2Gt1, D95)
→ T4_2` (`gm_T4_2Pair_of_one`, `gm_T4_2Gt1S_of_pair`, `gm_T4_2Gt1E_of_strict`, `gm_T4_2_of_gt1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric.GM

/-- **GM Theorem 4.2 from `T4_2PairOne`** -/
theorem gm_T4_2_of_pairOne (H : T4_2PairOne) : T4_2 :=
  gm_T4_2_of_gt1 (gm_T4_2Gt1E_of_strict (gm_T4_2Gt1S_of_pair (gm_T4_2Pair_of_one H)))

end LQGMetric.GM
