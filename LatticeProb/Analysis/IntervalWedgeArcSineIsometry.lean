import LatticeProb.Analysis.IntervalSineHilbertBasis
import LatticeProb.Analysis.WedgeArcSineComplete

/-! # The sine-basis isometry between an interval and a circular arc -/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb

/-- The isometry matching the normalized sine bases of the symmetric interval
and the circular arc of the same opening. -/
noncomputable def intervalWedgeArcSineIsometry {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) :
    Lp ℂ 2 (volume.restrict (Ioo (-θ / 2) (θ / 2))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (wedgeArcSurfaceMeasure θ) :=
  (intervalSineHilbertBasis (show -θ / 2 < θ / 2 by linarith)).repr.trans
    (wedgeArcSineHilbertBasis hθ hθ').repr.symm

/-- The isometry sends each normalized interval sine to its angular counterpart. -/
@[simp] theorem intervalWedgeArcSineIsometry_apply_mode {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) :
    intervalWedgeArcSineIsometry hθ hθ'
      (intervalNormalizedSineLp (-θ / 2) (θ / 2) n) = wedgeArcSineLp θ n := by
  change (wedgeArcSineHilbertBasis hθ hθ').repr.symm
    ((intervalSineHilbertBasis (show -θ / 2 < θ / 2 by linarith)).repr
      (intervalNormalizedSineLp (-θ / 2) (θ / 2) n)) = _
  rw [← intervalSineHilbertBasis_apply (show -θ / 2 < θ / 2 by linarith) n,
    HilbertBasis.repr_self,
    HilbertBasis.repr_symm_single, wedgeArcSineHilbertBasis_apply]

/-- The inverse isometry sends each angular sine to the corresponding interval sine. -/
@[simp] theorem intervalWedgeArcSineIsometry_symm_apply_mode {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 2 * Real.pi) (n : ℕ) :
    (intervalWedgeArcSineIsometry hθ hθ').symm (wedgeArcSineLp θ n) =
      intervalNormalizedSineLp (-θ / 2) (θ / 2) n := by
  rw [← intervalWedgeArcSineIsometry_apply_mode hθ hθ' n,
    LinearIsometryEquiv.symm_apply_apply]

end LatticeProb
