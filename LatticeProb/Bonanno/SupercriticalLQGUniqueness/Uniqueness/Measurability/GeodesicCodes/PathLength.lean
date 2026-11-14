/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.PathLength at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap




 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

abbrev Path := C(unitInterval, ℂ)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes
