import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! # Radial cones over the unit sphere -/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace LatticeProb

/-- The cone over a subset of the unit sphere consists of points whose normalized
    directions lie in that subset and whose norms lie in the open unit interval. -/
theorem radialCone_unitSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (hs : ∀ x ∈ s, ‖x‖ = 1) :
    Ioo (0 : ℝ) 1 • s = {x | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ ‖x‖⁻¹ • x ∈ s} := by
  ext x
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    have hn : ‖r • y‖ = r := by rw [norm_smul_of_nonneg hr.1.le, hs y hy, mul_one]
    refine ⟨by simpa [hn] using hr.1, by simpa [hn] using hr.2, ?_⟩
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr.1), one_smul]
    exact hy
  · rintro ⟨hpos, hlt, hx⟩
    refine ⟨‖x‖, ⟨hpos, hlt⟩, ‖x‖⁻¹ • x, hx, ?_⟩
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]

end LatticeProb
