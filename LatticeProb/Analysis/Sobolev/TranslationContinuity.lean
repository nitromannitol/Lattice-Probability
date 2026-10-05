/-
# A different low-frequency compactness route: uniform translation-continuity

The support-repair residuals `BandLimitedTestFnApproxOnDomain` and
`BandCentreSupportRepair` are **false** (`LatticeProbAudit/RELLICH-LOWFREQ-SUPPORT-REPAIR.md`,
commit `f73b92a`): a nonzero band-limited projection is not `H^{s₀}`-close to a test
function on a fixed bounded domain, because the latter vanishes off `D`.  The residual must
approximate the test function `φ` **itself**.

This module opens the classical **Fréchet–Kolmogorov** route to that statement: the
`H^s`-unit ball of `C_c^∞(D)` is relatively compact in `H^{s₀}(ℝ^d)` for `s₀ < s`, and the
proof needs, besides boundedness and the fixed compact support,

* **uniform translation-continuity**: `sup_φ ‖φ(·+h) − φ‖_{H^{s₀}} → 0` as `h → 0`.

The key algebraic input is the Fourier translation identity, which Mathlib has only for
`VectorFourier.fourierIntegral`; this module states it for the `𝓕` notation (`𝓕` is
definitionally that integral).  The quantitative bound is then

  `sobolevNormSq d s₀ (φ(·+h) − φ)`
    `≤ (2πR‖h‖)² · sobolevNormSq d s₀ φ + 4 · sobolevNormSqHigh d s₀ R φ`,

which gives uniform translation-continuity on the `H^s`-unit ball: the second term is
`≤ 4 (1+R²)^{s₀−s}`, uniformly small for large `R` because `s₀ < s`, and the first is
`(2πR‖h‖)²` for `‖φ‖_{H^{s₀}} ≤ 1`.
-/
import LatticeProb.Analysis.Sobolev.MollifierFourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The Fourier translation identity.**
`𝓕 (fun x => φ (x + h)) = fun ξ => 𝐞 ⟪h, ξ⟫ • 𝓕 φ ξ`.  This is
`VectorFourier.fourierIntegral_comp_add_right` for the `𝓕` notation; it is the input of
the uniform translation-continuity bound, since the phase factor `𝐞 ⟪h, ξ⟫ − 1` is small
for small `h` at bounded frequency. -/
theorem fourier_comp_add_right_lift {d : ℕ} (φ : Space d → ℂ) (h : Space d) :
    𝓕 (fun x => φ (x + h)) = fun ξ => 𝐞 (inner ℝ h ξ) • 𝓕 φ ξ := by
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space d))
      (fun x => φ (x + h))
    = fun ξ => 𝐞 (inner ℝ h ξ)
      • VectorFourier.fourierIntegral 𝐞 volume (innerₗ (Space d)) φ ξ
  exact VectorFourier.fourierIntegral_comp_add_right (μ := volume)
    (L := innerₗ (Space d)) Real.fourierChar φ h

end LatticeProb.Sobolev
