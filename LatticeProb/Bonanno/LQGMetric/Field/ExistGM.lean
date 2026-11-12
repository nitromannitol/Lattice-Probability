/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistGM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Defs

/-!
# `GM.ExistsNormalizedGFF` (blueprint M1 row 4 / §5, field layer `F.GFF-exist`; obligation N1)

Proved by `GFFExist.exists_normalizedWPGFF` (task P2-EXIST).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace GM

/-- **N1**: a normalized whole-plane GFF exists (`GM.ExistsNormalizedGFF`). -/
theorem existsNormalizedGFF : ExistsNormalizedGFF := GFFExist.exists_normalizedWPGFF

end GM
end LQGMetric
