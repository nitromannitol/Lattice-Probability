/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeRadial at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLqgQ
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLastZeroR

/-!
# Frozen definition: `MatedCRT.coneRadial`

For `t < 0`, the radial branch satisfies `c(ℓ − t) + Qt = B̂_{−t} + αt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **The radial process of the α-quantum cone** (DMS Def 4.10, DMS, with Rem 4.4,
DMS): `A_t = h_{e^{-t}}(0)`; `A_t = B_t + αt` for `t ≥ 0`; for `t < 0`, `A_t = B̂_{−t} + αt` where
`B̂_s + (Q − α)s = c(ℓ + s)` is the part after its last zero `ℓ` of `c(u) = B'_u + (Q − α)u` (Brownian motion with
drift `Q − α` conditioned to stay positive). -/
def coneRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then b t.toNNReal + α * t
  else
    (fun c : ℝ → ℝ => c (lastZeroR c - t) + lqgQ γ * t)
      (fun u => b' u.toNNReal + (lqgQ γ - α) * u)

end MatedCRT

end MatedCRTHarmonic
