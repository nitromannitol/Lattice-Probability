import LatticeProb.Analysis.AngularIntegralMeasurable
import LatticeProb.Analysis.RadialLocalIntegrability

/-!
# Planar and angular integrability of radial functions with a logarithmic bound

For a function `g : ℝ → ℝ`, continuous on `(0, ∞)` and bounded by `C (1 + |log t|)` on `(0, δ]`, the radial
function `z ↦ g ‖z‖` is locally integrable on `ℂ`, and its restriction to every circle through the origin is
interval integrable. The two conclusions are independent: a circle is Lebesgue-null, so the angular statement
does not follow from the planar one.

The planar statement is `LatticeProb.RadialLocalIntegrability.locallyIntegrable_radial`; the angular statement
for a circle centred at `z` with radius `r` is `LatticeProb.AngularIntegralMeasurable.intervalIntegrable_radial_circle`.
This module packages the two.
-/

open MeasureTheory Set Filter Topology

namespace LatticeProb.AngularLogIntegrability

/-- Planar and angular integrability of a radial function with a logarithmic bound. The function
`z ↦ g ‖z‖` is locally integrable on `ℂ`, and for every `z` and every `r > 0` with `‖z‖ = r` and `2 r ≤ δ`
the function `θ ↦ g ‖z + r e^{iθ}‖` is interval integrable on `[0, 2π]`. -/
theorem locallyIntegrable_radial_and_circle {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0)) {C δ : ℝ}
    (hδ : 0 < δ) (hbound : ∀ t : ℝ, 0 < t → t ≤ δ → |g t| ≤ C * (1 + |Real.log t|)) :
    LocallyIntegrable (fun z : ℂ => g ‖z‖) volume ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r → ‖z‖ = r → 2 * r ≤ δ →
        IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * Complex.exp (Complex.I * θ)‖) volume 0
          (2 * Real.pi) :=
  ⟨LatticeProb.RadialLocalIntegrability.locallyIntegrable_radial hg hδ hbound, fun _ _ hr hz hr2 =>
    LatticeProb.AngularIntegralMeasurable.intervalIntegrable_radial_circle hg hr hz hr2 hbound⟩

end LatticeProb.AngularLogIntegrability
