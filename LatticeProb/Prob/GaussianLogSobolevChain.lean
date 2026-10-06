/-
# The Gaussian log-Sobolev inequality in every dimension, from the Γ chain

`LatticeProb.GaussianLogSobolev n` is the frozen Gaussian log-Sobolev inequality and
`LatticeProb.GaussianHerbstBound n` its Herbst consequence.  The route to all `n` is the sharp
**gradient (Γ) form** `GaussianLogSobolevGrad n`, which tensorizes without the factor-two loss of
the Lipschitz form.  The landed pieces are

* `gaussianLogSobolevGrad_of_one_of_tensorStep` (`GaussianLogSobolevGrad.lean`):
  `Grad 1 → GradTensorStep → ∀ n, Grad (n+1)`;
* `gaussianLogSobolevGradTensorStep_of_prodStep` (`GaussianLogSobolevGradTensorProved.lean`):
  `Grad 1 → GradProdStep → GradTensorStep`, where `GradProdStep` is the abstract product
  tensorization `Grad m → Grad n → Grad (m+n)`.

This module composes them to the Γ-form inequality in every dimension, and then, through the
named **regularity bridge** `GaussianLogSobolevGradToLipschitz`, to the frozen
`GaussianLogSobolev n` and the Herbst bound `GaussianHerbstBound n`.

## The exact gap

The Γ-form predicate quantifies over `C¹` densities, while the frozen predicate quantifies over
all positive densities whose logarithm is merely Lipschitz.  Passing from the former to the latter
needs the a.e. differentiability of a Lipschitz function and a mollification/Dirichlet-energy
limit.  The a.e. differentiability is in Mathlib in every finite dimension
(`LipschitzWith.ae_differentiableAt`); the Dirichlet-energy limit is not.  That
passage is isolated as the named `Prop`
`GaussianLogSobolevGradToLipschitz`, never assumed.  The other input is the measure-theoretic
assembly `GaussianLogSobolevGradProdStep` (the entropy chain rule `entropy_prod_split`, the
weighted Jensen `norm_sq_integral_le_integral_norm_sq`, and the `piFinSuccAbove` transport).
-/
import LatticeProb.Prob.GaussianLogSobolevGradTensorProved

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- **The Γ-form inequality in every dimension `n ≥ 1`.**  From the one-dimensional Γ-form
inequality and the abstract product step, the landed induction and reduction give
`GaussianLogSobolevGrad (n + 1)` for every `n`. -/
theorem gaussianLogSobolevGrad_all_of_one_of_prodStep
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep) :
    ∀ n : ℕ, GaussianLogSobolevGrad (n + 1) :=
  gaussianLogSobolevGrad_of_one_of_tensorStep hone
    (gaussianLogSobolevGradTensorStep_of_prodStep hone hprod)

/-- **The regularity bridge: Γ-form ⟹ frozen Lipschitz form.**  The named gap between the `C¹`
densities of `GaussianLogSobolevGrad` and the merely Lipschitz-log densities of the frozen
`GaussianLogSobolev`.  The one-dimensional case of the underlying Rademacher theorem is
`LipschitzWith.ae_differentiableAt_real`, and the finite-dimensional case is
`LipschitzWith.ae_differentiableAt`; what is missing is the Dirichlet-energy limit. -/
def GaussianLogSobolevGradToLipschitz (n : ℕ) : Prop :=
  GaussianLogSobolevGrad n → GaussianLogSobolev n

/-- **The frozen Gaussian log-Sobolev inequality in every dimension.**  Composing the Γ-form chain
in all dimensions with the regularity bridge gives `GaussianLogSobolev n` for every `n` (the
`n = 0` case is `gaussianLogSobolev_zero`). -/
theorem gaussianLogSobolev_all_of_one_of_prodStep
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep)
    (hbridge : ∀ n : ℕ, GaussianLogSobolevGradToLipschitz n) :
    ∀ n : ℕ, GaussianLogSobolev n := by
  intro n
  cases n with
  | zero => exact gaussianLogSobolev_zero
  | succ n =>
      exact hbridge (n + 1) (gaussianLogSobolevGrad_all_of_one_of_prodStep hone hprod n)

/-- **The Herbst exponential moment bound in every dimension.**  Through the completed Herbst
chain `gaussianHerbstBound_of_logSobolev`, the general log-Sobolev inequality gives
`GaussianHerbstBound n` for every `n`. -/
theorem gaussianHerbstBound_all_of_one_of_prodStep
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep)
    (hbridge : ∀ n : ℕ, GaussianLogSobolevGradToLipschitz n) (n : ℕ) :
    GaussianHerbstBound n :=
  gaussianHerbstBound_of_logSobolev n
    (gaussianLogSobolev_all_of_one_of_prodStep hone hprod hbridge n)

end LatticeProb
