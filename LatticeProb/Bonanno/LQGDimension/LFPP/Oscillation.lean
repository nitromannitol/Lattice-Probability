/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Oscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux

/-!
# Node `L37` (`Draft.Oscillation37`): oscillation and segment average of `h_ε`

We prove, unconditionally (using the proved nodes `SegCombLaw`, `ChainingBox` and the Gaussian
concentration of maxima):

1. `ω_ε = osc (h_ε) (8ε) = o_P(log 1/ε)`: for every `κ > 0`,
   `P(κ log(1/ε) < ω_ε) → 0` as `ε ↓ 0`  (`Osc37.osc_tendsto`);
2. `⟨h_ε, ν_{[0,1]}⟩ = O_P(1)` uniformly in `ε ∈ (0,1)`  (`Osc37.segAvg_bounded`).

Proof of 1 (`OscillationAux`).  The circle-average covariance is
`C(z,w) = β(z) + β(w) - log ε - A(z,w)` with `A(z,z) = 0`, `0 ≤ A(z,w) ≤ |z-w|/ε`, so
`Var(h_ε z - h_ε w) ≤ 2|z-w|/ε`.  On a disc `B(g, 10ε)` chaining gives
`E max (h_ε z - h_ε g) ≤ C₀ = 20√5√240` for every finite family, and concentration gives
`P(max ≥ C₀ + s) ≤ exp(-s²/(10π²))`.  Continuity of `z ↦ h_ε(z)` and continuity of measures from
below pass this to the supremum over the whole disc.  A union bound over the `≤ 121 ε⁻²` points
of the grid `ε ℤ²` covering the disc of radius `3` gives
`P(ω_ε > κ log(1/ε)) ≤ 242 ε` for `ε` small.  (All events are handled through outer measure: no
measurability of `ω_ε` is needed.)

Proof of 2.  `⟨h_ε, ν_{[0,1]}⟩` is centered Gaussian with variance `∫∫ C(s, s') ≤ 2 + 3 log 2`,
from `C(z,w) ≤ -log|z-w| + 3 log 2` on the unit disc; conclude by Chebyshev.
-/

namespace LQGDimension

/-- **Node `L37`** (`Blueprint.Draft.Oscillation37`), unconditionally. -/
theorem oscillation37 : Blueprint.Draft.Oscillation37 := by
  intro Ω _ P h hG
  exact ⟨fun κ hκ => Osc37.osc_tendsto hG hκ, fun θ hθ => Osc37.segAvg_bounded hG hθ⟩

end LQGDimension
