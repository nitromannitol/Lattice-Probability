/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.CircleBox at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.OuterMoment
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CouplingTail

/-!
# A Gaussian tail on one circle-average box

For a normalized whole-plane GFF, the circle-average process at radius `r`
has variance at most `log(1/r) + O(1)` on a bounded box and increments of
variance at most `2|z-w|/r`. Borell--TIS and the pinned Fernique estimate
therefore give a tail with an `O(1)` supremum offset on a box of side `r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric LQGMetric

namespace MatedCRTHarmonic.GMCUpper

/-- A jointly continuous circle-average version of a normalized whole-plane
GFF has the same finite-dimensional Gaussian law as the canonical version. -/
theorem isGFFCircleAverage_of_version {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}
    (hX : IsNormalizedWPGFF X P)
    (hH : DFGPS.IsCircleAvgVersion X P H) :
    LQGDimension.IsGFFCircleAverage H P := by
  obtain ⟨H₀, hH₀, hG₀⟩ := exists_circleAvgVersion_normalized hX
  have hae : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] H₀ r z := by
    intro r hr z
    exact (hH.ae_eq r hr z).trans (hH₀.ae_eq r hr z).symm
  refine ⟨hG₀.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩
  · exact hG₀.isGaussianProcess.congr fun p => (hae p.1 p.1.2 p.2).symm
  · intro r hr z
    rw [integral_congr_ae (hae r hr z)]
    exact hG₀.integral_eq_zero r hr z
  · intro r hr s hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (hae r hr z) (hae s hs w)]
    exact hG₀.covariance_eq r hr s hs z w
  · intro r hr ω
    exact continuousOn_univ.1
      ((hH.cont ω).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun z _ => ⟨hr, mem_univ z⟩))

end MatedCRTHarmonic.GMCUpper
