import LatticeProb.Topology.StandardBrownianCurveSupport

/-! # Scalar Brownian curve laws with a prescribed starting point -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open LatticeProb.UnboundedRayIntervalIntegrand

namespace LatticeProb.UnboundedRayCurveSpace

noncomputable section

/-- Translating a continuous path in space. -/
def translatePath {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (f : Path d) : Path d :=
  ⟨fun t => z + f t, continuous_const.add f.continuous⟩

/-- Spatial translation is continuous on the continuous-path carrier. -/
theorem continuous_translatePath {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    Continuous (translatePath z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Path d × ℝ≥0 => z + p.1 p.2)
  fun_prop

/-- Translation preserves unbounded range. -/
theorem unbounded_range_translatePath {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (f : Path d) (hf : ¬ Bornology.IsBounded (Set.range f)) :
    ¬ Bornology.IsBounded (Set.range (translatePath z f)) := by
  intro h
  obtain ⟨R, hR⟩ := h.exists_norm_le
  apply hf
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R + ‖z‖, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hRt : ‖z + f t‖ ≤ R := hR _ ⟨t, rfl⟩
  calc
    ‖f t‖ = ‖(z + f t) - z‖ := by congr 1; abel
    _ ≤ ‖z + f t‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ R + ‖z‖ := add_le_add hRt le_rfl

/-- A scalar Brownian path law is the standard law with a linear time change. -/
theorem scalarBrownianLaw_eq_map_clock
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    {s : ℝ≥0} (hs : 0 < s) (hfac : target.factor = (s : ℝ) • 1) :
    (target.pathLaw : Measure (Path 2)) = (target.standardLaw : Measure (Path 2)).map
      (fun f => f.comp ⟨OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2),
        (OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)).continuous⟩) := by
  let μ : Measure (Path 2) := target.standardLaw
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)
  let F : Path 2 → Path 2 := fun f => f.comp ⟨φ, φ.continuous⟩
  have hF : Measurable F := (ContinuousMap.continuous_precomp ⟨φ, φ.continuous⟩).measurable
  change (target.pathLaw : Measure (Path 2)) = μ.map F
  rw [ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget.pathLaw,
    ReflectedGMS.StatementIngredients.anisotropicBrownianLaw, ProbabilityMeasure.toMeasure_map]
  change μ.map (ReflectedGMS.StatementIngredients.linearImageBrownianPath target.factor) = μ.map F
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

/-- At any common starting point, a positive scalar Brownian target and the standard
Brownian law have the same law on local curve classes. -/
theorem curveLaw_translated_scalarBrownian
    (target : ReflectedGMS.StatementIngredients.AnisotropicBrownianTarget)
    {s : ℝ≥0} (hs : 0 < s) (hfac : target.factor = (s : ℝ) • 1)
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
  let μ₀ : Measure (Path 2) := target.standardLaw
  let : IsProbabilityMeasure μ₀ := target.isStandard.1
  let T := translatePath z
  have hT : Measurable T := (continuous_translatePath z).measurable
  let μ := μ₀.map T
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  have hμ : ∀ᵐ (f : Path 2) ∂μ, ¬ Bornology.IsBounded (Set.range f) := by
    apply (ae_map_iff hT.aemeasurable (measurableSet_continuousMap_unbounded_range 0)).2
    filter_upwards [BouRabeeGwynne.ae_unbounded_range_standardBrownian (by decide) target.isStandard]
      with f hf
    exact unbounded_range_translatePath z f hf
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)
  let F : Path 2 → Path 2 := fun f => f.comp ⟨φ, φ.continuous⟩
  have hF : Measurable F := (ContinuousMap.continuous_precomp ⟨φ, φ.continuous⟩).measurable
  have hmap : (target.pathLaw : Measure (Path 2)).map T = μ.map F := by
    rw [scalarBrownianLaw_eq_map_clock target hs hfac]
    change (μ₀.map F).map T = (μ₀.map T).map F
    rw [Measure.map_map hT hF, Measure.map_map hF hT]
    congr 1
  obtain ⟨hν, hcurve⟩ := curveLaw_map_timeChange μ hμ φ F hF (by intro f t; rfl)
  refine ⟨hμ, ?_, ?_⟩
  · change ∀ᵐ (f : Path 2) ∂((target.pathLaw : Measure (Path 2)).map T),
      ¬ Bornology.IsBounded (Set.range f)
    rw [hmap]
    exact hν
  · change curveLaw ((target.pathLaw : Measure (Path 2)).map T) _ = curveLaw μ hμ
    simpa only [← hmap] using hcurve

end
end LatticeProb.UnboundedRayCurveSpace
