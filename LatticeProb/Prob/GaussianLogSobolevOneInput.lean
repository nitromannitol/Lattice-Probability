/-
# The one-dimensional Gaussian log-Sobolev inequality: the last input of the general-`n` chain

`LatticeProb.GaussianLogSobolevOne = GaussianLogSobolev 1` is the one-dimensional Gaussian
log-Sobolev inequality (Gross 1975; Bakry–Émery 1985): for a positive density `h` on `ℝ` with
`∫ h ∂γ = 1`, `γ = gaussianReal 0 1`, and `log ∘ h` `C`-Lipschitz,
`∫ h log h ∂γ ≤ C²/2`.

The general-`n` chain composed at `9f18f9a` (`GaussianLogSobolevGeneral.lean`) takes the sharp
**Γ-form** one-dimensional inequality `GaussianLogSobolevGrad 1` together with the abstract product
step `GaussianLogSobolevGradProdStep` and the regularity bridge.  This module records that
`GaussianLogSobolevOne` follows from those inputs, and names the exact missing Mathlib declaration.

## The exact missing declaration

Mathlib and the library contain **no** Gaussian log-Sobolev, Poincaré, Bakry–Émery,
Brascamp–Lieb
or Bobkov/Prékopa–Leindler result (`grep -rli "logsobolev\|poincareinequality\|brascamp\|prekopa\
\|bobkov" .lake/packages/mathlib/Mathlib` is empty).  The single missing input is the Γ-form
one-dimensional inequality

```lean
def GaussianLogSobolevGradOne : Prop := GaussianLogSobolevGrad 1
```

i.e. `∫ h log h ∂γ ≤ (1/2) ∫ (log h)'² h ∂γ` for positive `C¹` `h` with
`∫ h ∂γ = 1`.  The standard route is the Ornstein–Uhlenbeck / heat-flow argument: with
`w_t = P_t h`, the entropy dissipation `d/dt Ent(w_t) = -I(t)` and the Fisher decay
`I'(t) ≤ -2 I(t)` give `Ent(h) ≤ I(0)/2`, where `I(t) = ∫ (log w_t)'² w_t ∂γ`.
The semigroup and generator are landed (`Prob/GaussianLogSobolevOU.lean`: `ouSemigroup`,
`ouGenerator`, and the named `OUHeatEquation`); the two integrations by parts against `γ` and
the `Γ₂` identity are the missing layer, and neither is in Mathlib.
-/
import LatticeProb.Prob.GaussianLogSobolevGeneral

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- **The exact missing Mathlib declaration.**  The one-dimensional Γ-form Gaussian log-Sobolev
inequality: `∫ h log h ∂γ ≤ (1/2) ∫ ‖∇ (log ∘ h)‖² h ∂γ`
for positive `C¹` `h` with `∫ h ∂γ = 1`.
It implies `GaussianLogSobolevOne` (`gaussianLogSobolevOne_of_gradOne`) and feeds the general-`n`
chain (`gaussianHerbstBound_of_gradOne`). -/
def GaussianLogSobolevGradOne : Prop :=
  GaussianLogSobolevGrad 1

/-- **The one-dimensional Gaussian log-Sobolev inequality**, from the Γ-form inequality and the
regularity bridge that extends it from `C¹` to merely Lipschitz-log densities. -/
theorem gaussianLogSobolevOne_of_gradOne
    (hgrad : GaussianLogSobolevGradOne)
    (hbridge : GaussianLogSobolevGradToLipschitz 1) :
    GaussianLogSobolevOne :=
  hbridge hgrad

/-- **The general-`n` chain with the last input supplied.**  With the Γ-form one-dimensional
inequality, the abstract product step and the regularity bridge, the Herbst exponential moment
bound holds in every dimension (via `gaussianHerbstBound_all_of_one_of_prodStep`, `9f18f9a`). -/
theorem gaussianHerbstBound_of_gradOne
    (hone : GaussianLogSobolevGradOne) (hprod : GaussianLogSobolevGradProdStep)
    (hbridge : ∀ n : ℕ, GaussianLogSobolevGradToLipschitz n) (n : ℕ) :
    GaussianHerbstBound n :=
  gaussianHerbstBound_all_of_one_of_prodStep hone hprod hbridge n

/-- **The Γ-form one-dimensional inequality is the only dimension-specific input.**  Every
`GaussianLogSobolev n` and `GaussianHerbstBound n` in the chain rests on `GaussianLogSobolevGradOne`
together with the dimension-uniform inputs `GaussianLogSobolevGradProdStep` and
`GaussianLogSobolevGradToLipschitz`; this is the precise content of `9f18f9a` with the last input
named. -/
theorem gaussianLogSobolev_all_of_gradOne
    (hone : GaussianLogSobolevGradOne) (hprod : GaussianLogSobolevGradProdStep)
    (hbridge : ∀ n : ℕ, GaussianLogSobolevGradToLipschitz n) :
    ∀ n : ℕ, GaussianLogSobolev n :=
  gaussianLogSobolev_all_of_one_of_prodStep hone hprod hbridge

end LatticeProb
