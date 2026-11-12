/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Sq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputs
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6

/-!
# DDDF Proposition 29 on the square `D = (−1,2)²`

DDDF = Ding–Dubédat–Dunlap–Falconet arXiv:1904.08021, `tightness.tex`, Proposition 29
(`Prop:GffHT`, l. 1500–1506). `Blueprint.DDDFProp29` states it for every bounded open `D`; DFGPS
(arXiv:1905.00380, T:877–881) uses it only for `D = (−1,2)²` (`DFGPS.zb_step`,
blueprint/DDDF.md l. 36). `DDDFProp29Sq` is the statement for that one domain and every `U ⋐ D`,
and `dddfProp29Sq_of` shows it is a special case of `Blueprint.DDDFProp29`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DDDF

open Blueprint HeatSq

/-- **DDDF Proposition 29** (`Prop:GffHT`, DD:1500–1506) for `D = (−1,2)²` and every open `U`
with `cl U` compact in `D` (see `Blueprint.DDDFProp29Coupling`). -/
def DDDFProp29Sq : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsCompact (closure U) →
    closure U ⊆ ((sqOpens (-1) 3 : TopologicalSpace.Opens ℂ) : Set ℂ) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      DDDFProp29Coupling (sqOpens (-1) 3) U C c t

end DDDF
end LQGMetric
