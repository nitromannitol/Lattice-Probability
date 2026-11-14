import LatticeProb.LQG.ShiftedCellDilation
import LatticeProb.LQG.ShiftedGridContinuousWalk

/-! # Dilation of shifted-grid walk interpolations -/

set_option autoImplicit false

open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Spatial scaling commutes with constant-step affine interpolation. -/
theorem path_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c m : ℝ) (p : ℕ → E) (t : ℝ≥0) :
    path m (fun n => c • p n) t = c • path m p t := by
  simp only [path, AffineMap.lineMap_apply_module, smul_add, smul_smul]
  congr 1 <;> rw [mul_comm]

end LatticeProb.ConstantStepInterpolation

namespace LatticeProb

/-- Spatial and time dilation identify the interpolated walks on corresponding grids. -/
theorem shiftedGridWalk_dilation (η η' : C(ℝ, ℂ)) (c b d θ m : ℝ)
    (hη : ∀ t, η' t = c • η (b * t)) (walk : ℕ → ℤ) (t : ℝ≥0) :
    ConstantStepInterpolation.path m
        (fun n => shiftedGridAnchor η' d θ (walk n)) t =
      c • ConstantStepInterpolation.path m
        (fun n => shiftedGridAnchor η (b * d) θ (walk n)) t := by
  have hanchors : (fun n => shiftedGridAnchor η' d θ (walk n)) =
      (fun n => c • shiftedGridAnchor η (b * d) θ (walk n)) := by
    funext n
    exact shiftedGridAnchor_rescale η η' (fun z => c • z) b d θ hη (walk n)
  rw [hanchors, ConstantStepInterpolation.path_smul]

end LatticeProb
