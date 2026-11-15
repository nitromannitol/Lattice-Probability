import LatticeProb.Topology.UnboundedRayTimeChangeLaw
import LatticeProb.Bonanno.ReflectedGMS.Process.QuenchedLimit

/-! # Local curve laws of scalar Brownian motions -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

/-- Positive scalar images of standard planar Brownian motion have the same
local curve law as the original motion. -/
theorem curveLaw_scalarBrownian
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    {s : ℝ≥0} (hs : 0 < s) (hfac : target.factor = (s : ℝ) • 1)
    (hμ : ∀ᵐ (f : Path 2) ∂(target.standardLaw : Measure (Path 2)),
      ¬ Bornology.IsBounded (Set.range f)) :
    ∃ hν : ∀ᵐ (f : Path 2) ∂(target.pathLaw : Measure (Path 2)),
      ¬ Bornology.IsBounded (Set.range f),
      curveLaw (target.pathLaw : Measure (Path 2)) hν =
        curveLaw (target.standardLaw : Measure (Path 2)) hμ := by
  let μ : Measure (Path 2) := target.standardLaw
  let : IsProbabilityMeasure μ := target.isStandard.1
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)
  let F : Path 2 → Path 2 := fun f => f.comp ⟨φ, φ.continuous⟩
  have hF : Measurable F := (ContinuousMap.continuous_precomp ⟨φ, φ.continuous⟩).measurable
  have hval : ∀ f t, F f t = f (φ t) := by intro f t; rfl
  have hmap : (target.pathLaw : Measure (Path 2)) = μ.map F := by
    rw [ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget.pathLaw,
      ReflectedGMS.StatementIngredients.anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map]
    change μ.map (ReflectedGMS.StatementIngredients.linearImageBrownianPath target.factor) =
      μ.map F
    calc
      _ = μ.map (F ∘ BouRabeeGwynne.scaledBrownianPath s⁻¹) := by
        congr 1
        funext f
        apply ContinuousMap.ext
        intro t
        have ht : s⁻¹ ^ 2 * (s ^ 2 * t) = t := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hs.ne', one_pow, one_mul]
        have himage : ReflectedGMS.StatementIngredients.linearImageBrownianPath
            ((s : ℝ) • 1) f t = (s : ℝ) • f t := by
          ext i
          fin_cases i <;>
            simp [ReflectedGMS.StatementIngredients.linearImageBrownianPath_apply, Matrix.one_apply]
        change ReflectedGMS.StatementIngredients.linearImageBrownianPath target.factor f t =
          BouRabeeGwynne.scaledBrownianPath s⁻¹ f (s ^ 2 * t)
        rw [hfac, himage, BouRabeeGwynne.scaledBrownianPath_apply, ht]
        simp
      _ = (μ.map (BouRabeeGwynne.scaledBrownianPath s⁻¹)).map F :=
        (Measure.map_map hF (BouRabeeGwynne.measurable_scaledBrownianPath _)).symm
      _ = μ.map F := by
        rw [BouRabeeGwynne.standardBrownianLaw_map_scale target.isStandard (inv_pos.2 hs)]
  obtain ⟨hν, hcurve⟩ := curveLaw_map_timeChange μ hμ φ F hF hval
  refine ⟨?_, ?_⟩
  · simpa only [hmap] using hν
  · simpa only [hmap] using hcurve

end
end LatticeProb.UnboundedRayCurveSpace
