/-
# The mvbe Sazonov assembly: the `m^{1/4}` balance and the analytic inputs

`OrthantSmoothing.lean` closed the C1 chain (kernel `orthantSmooth`, Fourier factor
`orthantFourierFactor`, one-dimensional half-line factors, and the transform identity
`halfLineFourierFactor_eq`), and `MultivariateSmoothing.lean` weighted the Sazonov remainder by that
factor (`sazonovWeightedRemainder`) and stated `mvbeSazonovSmoothing`.  This module assembles the
remaining C1 pieces:

* `sazonov_balance_closure` — **the `m^{1/4}` balance, closed**: at the balanced bandwidth
  `T = m^{3/4}` (where `sazonovTail m T = m^{1/4}`, `sazonovTail_bandwidth`) the total bound
  `C m^{1/4} (1 + δ⁻¹) W + sazonovTail m T` factors as `m^{1/4} · (C (1 + δ⁻¹) W + 1)`, so the
  dimension factor is closed out front;
* `SazonovSmoothedDifferenceBound` — the named `B`-input of the deconvolution
  `orthant_smoothing_of_smoothed`: the Gaussian-smoothed orthant difference is bounded by the
  `orthantFourierFactor`-weighted Sazonov remainder;
* `SazonovGaussianKernelTail` — the named tail input `∫_{∃ j, h < |w j|} k ≤ a / h` for the Gaussian
  smoothing kernel.

The two `Prop`s are the remaining analytic content; neither is assumed anywhere as an axiom.
-/
import Mathlib
import LatticeProb.Prob.OrthantSmoothing
import LatticeProb.Prob.MultivariateEsseenDeconvolution

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- **The `m^{1/4}` balance closure.**  At the balanced bandwidth `T = m^{3/4}` — where the
Gaussian tail equals the dimension factor, `sazonovTail m (m^{3/4}) = m^{1/4}`
(`sazonovTail_bandwidth`) — the total Sazonov bound
`C m^{1/4} (1 + δ⁻¹) W + sazonovTail m T` is `m^{1/4} · (C (1 + δ⁻¹) W + 1)`. -/
theorem sazonov_balance_closure {m : ℕ} (hm : 0 < m) (C δ W : ℝ) :
    C * ((m : ℝ) ^ ((1 : ℝ) / 4) * (1 + δ⁻¹)) * W + sazonovTail m ((m : ℝ) ^ ((3 : ℝ) / 4))
      = (m : ℝ) ^ ((1 : ℝ) / 4) * (C * (1 + δ⁻¹) * W + 1) := by
  rw [sazonovTail_bandwidth hm]
  ring

/-- **The Sazonov smoothed-difference bound** — the named `B`-input of
`orthant_smoothing_of_smoothed`.  For the Gaussian smoothing kernel `gaussDensityVec σ`, the
kernel-smoothed difference of the orthant CDFs is bounded by the `orthantFourierFactor`-weighted
Sazonov remainder `sazonovWeightedRemainder σ μ γ T` with the dimension factor `m^{1/4}` and the
near-isotropy factor `1 + δ⁻¹`.  This is the Fourier-inversion content of C1; it is never assumed as
an axiom. -/
def SazonovSmoothedDifferenceBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (σ T δ : ℝ) (μ γ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure γ],
      0 < σ → 0 < T → 0 < δ →
      ∀ x : Fin m → ℝ,
        |∫ w, ((μ {y : Fin m → ℝ | ∀ j, y j ≤ x j - w j}).toReal -
            (γ {y : Fin m → ℝ | ∀ j, y j ≤ x j - w j}).toReal) * gaussDensityVec σ w ∂volume| ≤
          C * ((m : ℝ) ^ ((1 : ℝ) / 4) * (1 + δ⁻¹)) * sazonovWeightedRemainder σ μ γ T

/-- **The Gaussian smoothing-kernel tail bound** — the named `a`-input of
`orthant_smoothing_of_smoothed`: the mass of `gaussDensityVec σ` outside the coordinate tube
`{∃ j, h < |w j|}` is at most `a / h`. -/
def SazonovGaussianKernelTail : Prop :=
  ∃ a : ℝ, 0 < a ∧
    ∀ (m : ℕ) (σ h : ℝ), 0 < σ → 0 < h →
      ∫ w in {w : Fin m → ℝ | ∃ j, h < |w j|}, gaussDensityVec σ w ∂volume ≤ a / h

/-- **`gaussFourier1` at `σ = √v`.**  The Gaussian Fourier factor at `σ = √v` is the real damping
`exp (-v t² / 2)`, since `(√v)² = v`. -/
theorem gaussFourier1_sqrt (v : ℝ≥0) (t : ℝ) :
    gaussFourier1 (Real.sqrt v) t = Real.exp (-((v : ℝ) * t ^ 2) / 2) := by
  rw [gaussFourier1, show (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) from Real.sq_sqrt v.2]

/-- **The half-line Fourier factor is the Gaussian factor times the shift phase.**  The half-line
Fourier factor `halfLineFourierFactor c v` — the transform of the shifted Gaussian density
`halfLineDensity c v` (`halfLineFourierFactor_eq`, step 11) — is the Gaussian Fourier factor
`gaussFourier1 √v` multiplied by the half-line shift phase `e^{i c t}`.  This is the connection the
Fourier inversion of `SazonovSmoothedDifferenceBound` uses. -/
theorem halfLineFourierFactor_eq_gauss (c : ℝ) (v : ℝ≥0) (t : ℝ) :
    halfLineFourierFactor c v t
      = Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) * (gaussFourier1 (Real.sqrt v) t : ℂ) := by
  rw [halfLineFourierFactor, gaussFourier1_sqrt, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end LatticeProb
