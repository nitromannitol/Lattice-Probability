import LatticeProb.LQG.PeanosphereContactContinuity

/-! # Finite fibres of Peanosphere contact paths -/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.RouteM

/-- Finite fibres of the curve imply finite fibres of the left contact path
on the levels strictly below the contour at the base time. -/
theorem Peanosphere.finite_fibre_eta_ellMinus {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (t : ℝ) (z : ℂ)
    (hfinite : (η ⁻¹' {z}).Finite) :
    {level ∈ Iio (lCoord ω t) | η (ellMinus ω t level) = z}.Finite := by
  apply (hfinite.image (lCoord ω)).subset
  intro level hlevel
  refine ⟨ellMinus ω t level, ?_, ellMinus_level P hlevel.1⟩
  simpa only [mem_preimage, mem_singleton_iff] using hlevel.2

/-- Finite fibres of the curve imply finite fibres of the right contact path
on the levels strictly below the contour at the base time. -/
theorem Peanosphere.finite_fibre_eta_rhoMinus {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) (t : ℝ) (z : ℂ)
    (hfinite : (η ⁻¹' {z}).Finite) :
    {level ∈ Iio (rCoord ω t) | η (rhoMinus ω t level) = z}.Finite := by
  apply (hfinite.image (rCoord ω)).subset
  intro level hlevel
  refine ⟨rhoMinus ω t level, ?_, rhoMinus_level P hlevel.1⟩
  simpa only [mem_preimage, mem_singleton_iff] using hlevel.2

end MatedCRTHarmonic.RouteM
