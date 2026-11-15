import LatticeProb.Topology.IsotropicBrownianFactorLaw
import LatticeProb.Topology.TranslatedScalarBrownianCurveLaw

/-! # Translated isotropic Brownian curve laws -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

/-- Isotropic Brownian motion and standard Brownian motion, translated to a common
starting point, have the same law on local curve classes. -/
theorem curveLaw_translated_isotropicBrownian
    (target : AnisotropicBrownianTarget) {c : ℝ≥0} (hc : 0 < c)
    (hcov : target.covariance = (c : ℝ) • 1)
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
  let s : ℝ≥0 := NNReal.sqrt c
  have hs : 0 < s := NNReal.sqrt_pos.2 hc
  have hss : (s : ℝ) * s = c := by
    change (NNReal.sqrt c : ℝ) * NNReal.sqrt c = c
    rw [← NNReal.coe_mul, NNReal.mul_self_sqrt]
  let scalarTarget : AnisotropicBrownianTarget :=
    { target with
      factor := (s : ℝ) • 1
      covariance_eq := by
        rw [hcov]
        simp only [covarianceOfBrownianFactor, Matrix.transpose_smul, Matrix.transpose_one,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hss] }
  have hlaw : (target.pathLaw : Measure (Path 2)) = scalarTarget.pathLaw := by
    rw [LatticeProb.isotropicBrownian_pathLaw_eq_scalar_image target hc hcov horth]
    rfl
  obtain ⟨hμ, hν, hcurve⟩ := curveLaw_translated_scalarBrownian scalarTarget hs rfl z
  refine ⟨hμ, ?_, ?_⟩
  · simpa only [hlaw] using hν
  · simpa only [hlaw] using hcurve

end
end LatticeProb.UnboundedRayCurveSpace
