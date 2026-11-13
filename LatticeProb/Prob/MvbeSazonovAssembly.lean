/-
# The Sazonov balance and the Gaussian half-line factors

`OrthantSmoothing.lean` builds the Gaussian-smoothed orthant kernel `orthantSmooth`, its Fourier
factor `orthantFourierFactor`, the one-dimensional half-line factors with the transform identity
`halfLineFourierFactor_eq`, and the weighted Sazonov remainder `sazonovWeightedRemainder`.  This
module adds:

* `sazonov_balance_closure` — **the `m^{1/4}` balance**: at the balanced bandwidth `T = m^{3/4}`
  (where `sazonovTail m T = m^{1/4}`, `sazonovTail_bandwidth`) the total bound
  `C m^{1/4} (1 + δ⁻¹) W + sazonovTail m T` factors as `m^{1/4} · (C (1 + δ⁻¹) W + 1)`, so the
  dimension factor is out front;
* `gaussFourier1_sqrt`, `halfLineFourierFactor_eq_gauss` — the half-line Fourier factor as the
  Gaussian factor `gaussFourier1 √v` times the shift phase `e^{i c t}`.
-/
import Mathlib
import LatticeProb.Prob.OrthantSmoothing

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

/-- **`gaussFourier1` at `σ = √v`.**  The Gaussian Fourier factor at `σ = √v` is the real damping
`exp (-v t² / 2)`, since `(√v)² = v`. -/
theorem gaussFourier1_sqrt (v : ℝ≥0) (t : ℝ) :
    gaussFourier1 (Real.sqrt v) t = Real.exp (-((v : ℝ) * t ^ 2) / 2) := by
  rw [gaussFourier1, show (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) from Real.sq_sqrt v.2]

/-- **The half-line Fourier factor is the Gaussian factor times the shift phase.**  The half-line
Fourier factor `halfLineFourierFactor c v` — the transform of the shifted Gaussian density
`halfLineDensity c v` (`halfLineFourierFactor_eq`) — is the Gaussian Fourier factor
`gaussFourier1 √v` multiplied by the half-line shift phase `e^{i c t}`. -/
theorem halfLineFourierFactor_eq_gauss (c : ℝ) (v : ℝ≥0) (t : ℝ) :
    halfLineFourierFactor c v t
      = Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) * (gaussFourier1 (Real.sqrt v) t : ℂ) := by
  rw [halfLineFourierFactor, gaussFourier1_sqrt, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end LatticeProb
