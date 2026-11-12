/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.M1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Assembly
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable

/-!
# Milestone M1: Theorems 1.1 and 1.2 of Gwynne–Miller from three cited results

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Theorems 1.1, 1.2 assuming Theorem 1.9, l. 582–593 (`blueprint/M1.md` §3 rows 24–25).
The three hypotheses are the Blueprint Props `GMWeakUniqueness` (GM Theorem 1.9),
`DFGPSExistence` (DFGPS Theorem 1.2) and `DFGPSScaling` (DFGPS Theorem 1.5); the field-layer
inputs (existence of a normalized GFF, measurability of the LFPP crossing) are proved theorems
(`GM.existsNormalizedGFF`, `LFPP.aemeasurable_lfppCross_normGFFLaw`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric

/-- **GM Theorem 1.2** (existence and uniqueness of the LQG metric) from GM Theorem 1.9 and
DFGPS Theorems 1.2 and 1.5 (GM l. 582–593). -/
theorem theorem12_of_blueprint (h19 : Blueprint.GMWeakUniqueness)
    (h12 : Blueprint.DFGPSExistence) (h15 : Blueprint.DFGPSScaling) : Theorem12 :=
  GM.theorem12_of_measurable (fun ξ ε hε => LFPP.aemeasurable_lfppCross_normGFFLaw ξ ε hε)
    h19 h12 h15

end LQGMetric
