/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFModel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxConnected
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFGaussian

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

 
def boxDGFF (n : ℕ) : Measure (EuclideanSpace ℝ (DGFFSite n)) :=
  (boxConductances n).gaussianOfPrecision (box_precision_posDef n)

instance (n : ℕ) : IsProbabilityMeasure (boxDGFF n) := by
  unfold boxDGFF WiredConductances.gaussianOfPrecision
  infer_instance

theorem boxDGFF_covariance (n : ℕ) (z w : DGFFSite n) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => h z,
      fun h : EuclideanSpace ℝ (DGFFSite n) => h w; boxDGFF n] =
      (Real.pi / 2) * (boxConductances n).algebraicGreen z w := by
  exact (boxConductances n).covariance_gaussianOfPrecision
    (box_precision_posDef n) z w

 
theorem boxDGFF_mean (n : ℕ) :
    ∫ h : EuclideanSpace ℝ (DGFFSite n), h ∂(boxDGFF n) = 0 := by
  unfold boxDGFF WiredConductances.gaussianOfPrecision
  exact integral_id_multivariateGaussian

end SupercriticalLQGUniqueness.B2.QPos
