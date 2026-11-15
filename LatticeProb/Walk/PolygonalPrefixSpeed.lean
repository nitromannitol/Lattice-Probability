import LatticeProb.Walk.PolygonalPrefixIdentity

/-! # Positive-speed polygonal path prefixes -/

set_option autoImplicit false
noncomputable section

open BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped NNReal unitInterval

namespace LatticeProb

/-- A normalized prefix at a knot is independent of the positive speed. -/
theorem normalizedPathPrefix_constantStep_knot_eq_polygonalCurve
    (p : ℕ → Plane) {m : ℝ≥0} (hm : 0 < m) (N : ℕ) :
    normalizedPathPrefix (ConstantStepInterpolation.continuousPlanePath m p)
      (ConstantStepInterpolation.knot m N) = polygonalCurve p id N := by
  rw [← normalizedPathPrefix_constantStep_eq_polygonalCurve]
  apply ContinuousMap.ext
  intro u
  rw [normalizedPathPrefix_apply, normalizedPathPrefix_apply]
  change ConstantStepInterpolation.path m p _ = ConstantStepInterpolation.path 1 p _
  unfold ConstantStepInterpolation.path
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm)
  have ht : (m : ℝ) * ((u : ℝ) * (ConstantStepInterpolation.knot m N : ℝ)) =
      (1 : ℝ) * ((u : ℝ) * (N : ℝ)) := by
    simp only [ConstantStepInterpolation.knot, NNReal.coe_div, NNReal.coe_natCast]
    field_simp
  change (let t := (m : ℝ) * ((u : ℝ) * (ConstantStepInterpolation.knot m N : ℝ))
    AffineMap.lineMap (p ⌊t⌋₊) (p (⌊t⌋₊ + 1)) (t - ⌊t⌋₊)) =
    (let t := (1 : ℝ) * ((u : ℝ) * (N : ℝ))
    AffineMap.lineMap (p ⌊t⌋₊) (p (⌊t⌋₊ + 1)) (t - ⌊t⌋₊))
  rw [ht]

/-- Projection of the normalized knot prefix to curve space. -/
theorem normalizedPrefixCurve_constantStep_knot_eq_polygonalCurve
    (p : ℕ → Plane) {m : ℝ≥0} (hm : 0 < m) (N : ℕ) :
    normalizedPrefixCurve (ConstantStepInterpolation.continuousPlanePath m p)
      (ConstantStepInterpolation.knot m N) = CurveSpace.project (polygonalCurve p id N) := by
  rw [normalizedPrefixCurve, normalizedPathPrefix_constantStep_knot_eq_polygonalCurve p hm N]

/-- The discrete stopped polygonal curve is the prefix at its totalized exit knot. -/
theorem project_normalizedPathPrefix_constantStep_exit_eq_stoppedPolygonalCurve
    {V : Type*} (pos : V → Plane) (A : Set V) (ω : ℕ → V)
    {m : ℝ≥0} (hm : 0 < m) :
    BouRabeeGwynne.CurveSpace.project (normalizedPathPrefix
      (ConstantStepInterpolation.continuousPlanePath m (pos ∘ ω))
      (ConstantStepInterpolation.knot m ((FiniteConductanceNetwork.exitTime A ω).untopD 0))) =
      stoppedPolygonalCurve pos A ω := by
  rw [normalizedPathPrefix_constantStep_knot_eq_polygonalCurve (pos ∘ ω) hm]
  rfl

end LatticeProb
end
