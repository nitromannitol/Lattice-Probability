import LatticeProb.Prob.QuarterTurnCovariance
import LatticeProb.Topology.IsotropicTranslatedBrownianCurveLaw

/-! # Quarter-turn invariant Brownian curve laws -/

set_option autoImplicit false

open MeasureTheory Set
open ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

/-- A Brownian target with quarter-turn invariant covariance and standard Brownian
motion have the same local curve law after translation to a common starting point. -/
theorem curveLaw_translated_quarterTurnBrownian
    (target : AnisotropicBrownianTarget)
    (hrot : planarQuarterTurn * target.covariance * planarQuarterTurn.transpose =
      target.covariance)
    (horth : ∀ O : Matrix (Fin 2) (Fin 2) ℝ, O.transpose * O = 1 →
      (target.standardLaw : Measure (Path 2)).map (linearImageBrownianPath O) =
        target.standardLaw)
    (z : EuclideanSpace ℝ (Fin 2)) :
    let μ := (target.standardLaw : Measure (Path 2)).map (translatePath z)
    let ν := (target.pathLaw : Measure (Path 2)).map (translatePath z)
    let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff
      (continuous_translatePath z).measurable.aemeasurable).2 target.isStandard.1
    let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
      (continuous_translatePath z).measurable.aemeasurable).2 inferInstance
    ∃ hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f),
    ∃ hν : ∀ᵐ (f : Path 2) ∂ν, ¬ Bornology.IsBounded (Set.range f),
      curveLaw ν hν = curveLaw μ hμ := by
  obtain ⟨c, hc, hcov⟩ :=
    exists_pos_smul_one_of_quarterTurn_invariant target.covariance target.positiveDefinite hrot
  exact curveLaw_translated_isotropicBrownian target hc hcov horth z

end
end LatticeProb.UnboundedRayCurveSpace
