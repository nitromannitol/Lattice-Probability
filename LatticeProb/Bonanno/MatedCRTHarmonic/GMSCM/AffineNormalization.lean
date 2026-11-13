/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.AffineNormalization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.AffineTransport
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepShift

/-!
# Translation and circle-average normalization of a whole-plane GFF

The raw translate of a unit-normalized whole-plane GFF differs from its
unit-normalized translate by one Gaussian circle average. That scalar is
exactly the negative normalization increment of the normalized translate
between the circles centered at `-w` and `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric LQGMetric.GM LQGMetric.CircleAvg

namespace MatedCRTHarmonic.GMSCM

/-- The whole-plane GFF recentered after translation by `w`. -/
def recenteredTranslate {Ω : Type} (h : Ω → DistC) (w : ℂ) : Ω → DistC :=
  fun ω => addConst (affineComp 1 w (h ω)) (-circleAvg (h ω) 1 w)

/-- The recentered translate is a normalized whole-plane GFF with the original law. -/
theorem recenteredTranslate_normalized {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (w : ℂ) :
    IsNormalizedWPGFF (recenteredTranslate h w) P ∧
      P.map (recenteredTranslate h w) = P.map h := by
  let : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  exact ⟨LQGMetric.CONF.hlz_rescale hh.1 one_pos w,
    CircleAvg.map_affine_sub_circleAvg hh one_pos w⟩

/-- The raw affine translate equals its recentered version plus the random
circle average. This is a pointwise identity of distributions. -/
theorem rawTranslate_eq_recentered_addConst {Ω : Type} (h : Ω → DistC)
    (w : ℂ) (ω : Ω) :
    affineComp 1 w (h ω) =
      addConst (recenteredTranslate h w ω) (circleAvg (h ω) 1 w) := by
  simp only [recenteredTranslate, GFFLaw.addConst_addConst,
    neg_add_cancel, GFFLaw.addConst_zero']

/-- The random constant in the affine translate is the negative increment
between the old unit circle and the new unit circle. -/
theorem recenteredTranslate_cInc {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (w : ℂ) :
    ∀ᵐ ω ∂P, cInc (recenteredTranslate h w) 1 (-w) 1 0 ω =
      -circleAvg (h ω) 1 w := by
  have hA : IsWholePlaneGFF (fun ω => affineComp 1 w (h ω)) P :=
    hh.1.affineComp one_pos w
  filter_upwards [CircleAvg.ae_circleAvg_addConst hA (-w) one_pos,
    CircleAvg.ae_circleAvg_addConst hA 0 one_pos, hh.2]
    with ω hleft hright hzero
  simp only [cInc, recenteredTranslate, hleft, hright,
    GM.circleAvg_affineComp_one_at]
  simp [hzero]

end MatedCRTHarmonic.GMSCM
