/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgLaw at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Uniqueness of the law of the normalized whole-plane GFF

Corollaries of `ae_circleAvg_addConst` (this task) and the law-uniqueness machinery of
`LQGMetric.Field.GFFLaw` (task P2-FINV, `handoff/P2-FINV.md`):

* `map_eq_of_isNormalizedWPGFF`: two whole-plane GFFs normalized by `h_1(0) = 0` (GM l. 223–224)
  have the same law on `𝒟'(ℂ)`;
* `map_affine_normalized`: for a normalized `h`, `r > 0`, `z`, the field
  `h(r·+z) − (h(r·+z))_1(0)` has the law of `h`. (GM's form uses `h_r(z)` in place of
  `(h(r·+z))_1(0)`; their a.s. equality is the remaining leaf (b), see `handoff/P2-FCIRC.md`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace CircleAvg

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- **The law of a normalized whole-plane GFF is unique.** -/
theorem map_eq_of_isNormalizedWPGFF {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsNormalizedWPGFF h P) (hh' : IsNormalizedWPGFF h' P') : P.map h = P'.map h' :=
  GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0) (measurable_circleAvg_left 1 0)
    hh.1 hh'.1 (ae_circleAvg_addConst_one_zero hh.1) (ae_circleAvg_addConst_one_zero hh'.1)
    hh.2 hh'.2

/-- For a normalized whole-plane GFF, `h(r·+z) − (h(r·+z))_1(0)` has the law of `h`. -/
theorem map_affine_normalized {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    P.map (fun ω => addConst (affineComp r z (h ω)) (-(circleAvg (affineComp r z (h ω)) 1 0))) =
      P.map h :=
  GFFLaw.map_affine_normalized_ae (GFFLaw.integral_bumpTest 0 0) (measurable_circleAvg_left 1 0)
    hh.1 (ae_circleAvg_addConst_one_zero hh.1) hh.2 hr z
    (ae_circleAvg_addConst_one_zero (hh.1.affineComp hr z))

end CircleAvg
end LQGMetric
