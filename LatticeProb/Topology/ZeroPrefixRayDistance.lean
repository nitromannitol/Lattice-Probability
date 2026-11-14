import LatticeProb.Topology.ConstantCurveDistance
import LatticeProb.Topology.FinitePrefixRayDistance

/-! # Stopped rays with a zero-duration prefix -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- A stopped ray is within the finite-curve distance of a constant ray. -/
theorem reparamEDist_stopped_zero_left_le {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (U : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t 0)) (fun t => g (min t U)) ≤
      edist (normalizedPrefixCurve f 0) (normalizedPrefixCurve g U) := by
  have hconst : normalizedPrefixCurve f 0 = CurveSpace.mk (NormalizedCurve.const (f 0)) := by
    change CurveSpace.project (normalizedPathPrefix f 0) = _
    congr 1
    ext u
    simp only [normalizedPathPrefix_apply, NNReal.coe_zero, mul_zero,
      ContinuousMap.const_apply]
    rfl
  rw [hconst]
  change ReparamEDist.reparamEDist (fun t => f (min t 0)) (fun t => g (min t U)) ≤
    edist (CurveSpace.mk (NormalizedCurve.const (f 0)))
      (CurveSpace.mk ⟨normalizedPathPrefix g U⟩)
  rw [CurveSpace.edist_const_mk]
  refine (ReparamEDist.reparamEDist_le_iSup_edist _ _).trans (iSup_le fun s => ?_)
  simp only [min_eq_right zero_le]
  by_cases hU : U = 0
  · subst U
    have hu : normalizedPathPrefix g 0 (0 : unitInterval) = g 0 := by
      rw [normalizedPathPrefix_apply]
      apply congrArg g
      apply Subtype.ext
      norm_num
    simpa only [min_eq_right zero_le, hu] using
      (le_iSup (fun u : unitInterval => edist (f 0) (normalizedPathPrefix g 0 u)) 0)
  · have hUpos : 0 < (U : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hU)
    let u : unitInterval := ⟨(min s U : ℝ) / U, div_nonneg (min s U).property hUpos.le,
      (div_le_one hUpos).2 (by exact_mod_cast min_le_right s U)⟩
    have hu : normalizedPathPrefix g U u = g (min s U) := by
      rw [normalizedPathPrefix_apply]
      apply congrArg g
      apply Subtype.ext
      change ((min s U : ℝ) / U) * U = (min s U : ℝ)
      exact div_mul_cancel₀ _ (ne_of_gt hUpos)
    rw [← hu]
    exact le_iSup (fun u : unitInterval => edist (f 0) (normalizedPathPrefix g U u)) u

/-- The same bound when the second prefix has duration zero. -/
theorem reparamEDist_stopped_zero_right_le {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (T : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t T)) (fun t => g (min t 0)) ≤
      edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g 0) := by
  rw [ReparamEDist.reparamEDist_comm, edist_comm]
  exact reparamEDist_stopped_zero_left_le g f T

/-- Stopping one of the rays at zero preserves its finite-curve distance. -/
theorem reparamEDist_stopped_zero_left_eq {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (U : ℝ≥0) :
    ReparamEDist.reparamEDist (fun t => f (min t 0)) (fun t => g (min t U)) =
      edist (normalizedPrefixCurve f 0) (normalizedPrefixCurve g U) :=
  le_antisymm (reparamEDist_stopped_zero_left_le f g U)
    (normalizedPrefixCurve_edist_le_reparamEDist_stopped_all f g 0 U)

end LatticeProb
