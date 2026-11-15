import LatticeProb.Walk.CellConfigVisitPathLaw
import LatticeProb.Prob.NormalizedPrefixCurve
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties

/-! # Polygonal curves as normalized path prefixes -/

set_option autoImplicit false
noncomputable section

open BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped NNReal unitInterval

namespace LatticeProb

/-- A finite unit-speed polygonal path has the same normalized representative
as the polygonal curve through its first `N` steps. -/
theorem normalizedPathPrefix_constantStep_eq_polygonalCurve
    (p : ℕ → Plane) (N : ℕ) :
    normalizedPathPrefix (ConstantStepInterpolation.continuousPlanePath 1 p) N =
      polygonalCurve p id N := by
  apply ContinuousMap.ext
  intro u
  by_cases hN : N = 0
  · subst N
    rw [polygonalCurve_zero, normalizedPathPrefix_apply]
    convert (ConstantStepInterpolation.path_knot (m := 1) (by norm_num) p 0) using 1 <;>
      simp [ConstantStepInterpolation.continuousPlanePath, ConstantStepInterpolation.knot]
    congr 1
  by_cases hu : (u : ℝ) = 1
  · have hueq : u = 1 := Subtype.ext hu
    subst u
    rw [polygonalCurve_end, normalizedPathPrefix_apply]
    convert (ConstantStepInterpolation.path_knot (m := 1) (by norm_num) p N) using 1 <;>
      simp [ConstantStepInterpolation.continuousPlanePath, ConstantStepInterpolation.knot]
    congr 1
  · have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hnonneg : 0 ≤ (N : ℝ) * (u : ℝ) := mul_nonneg (Nat.cast_nonneg _) u.property.1
    have hlt : (N : ℝ) * (u : ℝ) < N := by
      nlinarith [show (0 : ℝ) < N by exact_mod_cast hNpos]
    let j := ⌊(N : ℝ) * (u : ℝ)⌋₊
    have hj : j < N := by
      exact (Nat.floor_lt hnonneg).2 hlt
    have hlo : (j : ℝ) ≤ (N : ℝ) * (u : ℝ) := Nat.floor_le hnonneg
    have hhi : (N : ℝ) * (u : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [polygonalCurve_on_segment_scaled p id hj u hlo hhi.le]
    change ConstantStepInterpolation.path 1 p ⟨(u : ℝ) * (N : ℝ), mul_nonneg u.property.1 (Nat.cast_nonneg _)⟩ = _
    unfold ConstantStepInterpolation.path
    dsimp only
    simp only [one_mul]
    change AffineMap.lineMap (p ⌊(u : ℝ) * N⌋₊) (p (⌊(u : ℝ) * N⌋₊ + 1))
      ((u : ℝ) * N - ⌊(u : ℝ) * N⌋₊) = _
    rw [show (u : ℝ) * N = (N : ℝ) * u from mul_comm _ _]
    change AffineMap.lineMap (p j) (p (j + 1)) ((N : ℝ) * u - j) = _
    simp only [AffineMap.lineMap_apply_module', Function.id_def]
    abel

/-- Projection gives the corresponding identity in the space of curves. -/
theorem normalizedPrefixCurve_constantStep_eq_polygonalCurve
    (p : ℕ → Plane) (N : ℕ) :
    normalizedPrefixCurve (ConstantStepInterpolation.continuousPlanePath 1 p) N =
      CurveSpace.project (polygonalCurve p id N) := by
  rw [normalizedPrefixCurve, normalizedPathPrefix_constantStep_eq_polygonalCurve]

end LatticeProb
end
