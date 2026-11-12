/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainOpenO at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Assembly.MainOpenL
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1

/-!
# Theorems 1.1 and 1.2 from the three remaining leaves, with the expectation form of DZZ L5.3

As `theorem11_openN`/`theorem12_openN` (Assembly/MainOpenN.lean), but with the leaf of DZZ
Lemma 5.3 part 1 (Ding–Zeitouni–Zhang arXiv:1807.00422) in the form the proved route uses:
`DZZ.DZZLem53ExpAll` (`∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ`, Papers/DZZ/S5L53W1.lean) in place of
`DZZInW.DZZLem53EventAll` (audit 2026-10-03-L, item L6; `DZZ.dzzLem53ExpAll_of_eventAll` shows the
new leaf is implied by the old one). `DG.DZZInputsDG` comes from `DZZ.dzzInputsDG_of_exp`, and
`CONFSection3` from `confSection3_openL` (Assembly/MainOpenL.lean). The remaining inputs are
`CONF.CONFLem2_10AtConfU` (D127), `CONFW.CONFThm3_9RestAll` (D130) and `DZZ.DZZLem53ExpAll` (D131);
`theorem11_openO_hbadB`/`theorem12_openO_hbadB` take `DZZ.L53HbadBAll` (the `hbadB` bound of
DEC-131 §2 at every `α* > 0`) in place of the last one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

open Blueprint

/-- **Theorem 1.2** from the three remaining leaves (expectation form of DZZ L5.3). -/
theorem theorem12_openO (hL : CONF.CONFLem2_10AtConfU) (hRest : CONFW.CONFThm3_9RestAll)
    (hexp : DZZ.DZZLem53ExpAll) : Theorem12 :=
  have hD : DG.DZZInputsDG := DZZ.dzzInputsDG_of_exp hexp
  theorem12_openK (confSection3_openL hL hRest hD) hD

/-- **Theorem 1.1** from the three remaining leaves (expectation form of DZZ L5.3). -/
theorem theorem11_openO (hL : CONF.CONFLem2_10AtConfU) (hRest : CONFW.CONFThm3_9RestAll)
    (hexp : DZZ.DZZLem53ExpAll) : Theorem11 :=
  have hD : DG.DZZInputsDG := DZZ.dzzInputsDG_of_exp hexp
  theorem11_openK (confSection3_openL hL hRest hD) hD

end LQGMetric
