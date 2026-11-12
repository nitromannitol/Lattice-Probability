/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_6Law at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable

/-!
# DFGPS Lemma 2.6, first identity: `D^{ε/r}_{h^r} =ᵈ D^{ε/r}_h`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) Lemma 2.6 (T:837–846): for a
whole-plane GFF `h` with `h_1(0) = 0` and `h^r := h(r·) − h_r(0)`, `h^r =ᵈ h`, hence
`D^{ε/r}_{h^r} =ᵈ D^{ε/r}_h`. The law identity `h^r =ᵈ h` is `GFFLaw.map_eq_of_normalized_ae`
with `(h(r·))_1(0) = h_r(0)` a.s. (`CircleAvg.ae_circleAvg_affineComp`); LFPP is a.s. a
measurable function of the field (`LFPP.lfppDistChain`, LFPP/Measurable.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- `h^r := h(r·) − h_r(0)` -/
def fieldScale (r : ℝ) (g : DistC) : DistC := addConst (affineComp r 0 g) (-circleAvg g r 0)

theorem isWholePlaneGFF_fieldScale (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) :
    IsWholePlaneGFF (fun ω => fieldScale r (h ω)) P :=
  (hh.affineComp hr 0).addConst ((measurable_circleAvg_left r 0).comp hh.measurable).neg

/-- `h^r =ᵈ h` for a whole-plane GFF normalized by `h_1(0) = 0`. -/
theorem map_fieldScale (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => fieldScale r (h ω)) = P.map h := by
  have hg := isWholePlaneGFF_fieldScale hh.1 hr
  have hn : ∀ᵐ ω ∂P, circleAvg (fieldScale r (h ω)) 1 0 = 0 := by
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero (hh.1.affineComp hr 0),
      CircleAvg.ae_circleAvg_affineComp hh.1 hr 0] with ω h1 h2
    simp only [fieldScale]
    rw [h1, h2]
    ring
  exact GFFLaw.map_eq_of_normalized_ae (GFFLaw.integral_bumpTest 0 0)
    (measurable_circleAvg_left 1 0) hg hh.1 (CircleAvg.ae_circleAvg_addConst_one_zero hg)
    (CircleAvg.ae_circleAvg_addConst_one_zero hh.1) hn hh.2

end LQGMetric.DFGPS
