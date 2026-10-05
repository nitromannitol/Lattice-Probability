/-
# The Γ tensorization assembly: status and the chain-rule component

The Γ-form Gaussian log-Sobolev tensorization
(`GaussianLogSobolevGradTensorStep`, `LatticeProb/Prob/GaussianLogSobolevGrad.lean`) needs the
assembly of the three landed analytic inputs:

* `LatticeProb.entropy_prod_split` (`GaussianLogSobolevGradTensor.lean`),
* `LatticeProb.norm_sq_integral_le_integral_norm_sq` (`GaussianLogSobolevGradTensor.lean`),
* `LatticeProb.hasFDerivAt_integral_marginal` (`FDerivIntegralMarginal.lean`).

This module lands the `fderiv`-of-`log` component of that assembly.  The remaining bookkeeping —
the weighted-measure Jensen on the probability measure `(h_x / F x) · ν`, the
`Measure.measurePreserving_piFinSuccAbove` transport of `γ_{n+1}` to `γ_1 ⊗ γ_n`, and the assembly —
is recorded below and is not yet formalised; the residual stays the named `Prop`
`GaussianLogSobolevGradTensorStep`.

## The assembly, precisely

Write `γ_m = Measure.pi (fun _ : Fin m => gaussianReal 0 1)`, split `Fin (n+1) ≃ Fin 1 × Fin n`,
write a density `h` with `x` the first and `y` the remaining coordinates, and let
`F x = ∫ y, h(x,y) ∂γ_n(y)`, `a(x,y) = ‖fderiv_x (log ∘ h) (x,y)‖`,
`b(x,y) = ‖fderiv_y (log ∘ h) (x,y)‖`, `b_F x = ‖fderiv_x (log ∘ F) x‖`.  Then

* `entropy_prod_split` gives `Ent(h) = ∫ F x · Ent(h_x / F x) dγ_1(x) + Ent(F)`;
* the slice `Γ`-LSI `GaussianLogSobolevGrad n` gives
  `F x · Ent(h_x / F x) ≤ (1/2) ∫ b(x,y)² h(x,y) ∂γ_n(y)`;
* the factor `Γ`-LSI `GaussianLogSobolevGrad 1` gives `Ent(F) ≤ (1/2) ∫ b_F x² F x dγ_1(x)`;
* `hasFDerivAt_integral_marginal` plus `fderiv_log` (below) write `fderiv (log ∘ F) x` as the
  weighted average `∫ fderiv_x (log ∘ h) (x,y) · (h(x,y)/F x) ∂γ_n(y)`, and
  `norm_sq_integral_le_integral_norm_sq` applied to the probability measure `(h_x/F x)·γ_n` gives
  `b_F x² F x ≤ ∫ a(x,y)² h(x,y) ∂γ_n(y)`.

Adding the two bounds gives `Ent(h) ≤ (1/2) ∫ (a² + b²) h ≤ (1/2) ∫ ‖∇ log h‖² h`, since on the
product with the sup norm `‖∇ log h‖ = a + b ≥ max(a,b)` and hence `‖∇ log h‖² ≥ a² + b²`.
-/
import LatticeProb.Prob.FDerivIntegralMarginal
import LatticeProb.Prob.GaussianLogSobolevGradTensor

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- The chain rule for the logarithm: if `F` is differentiable at `x` and `F x ≠ 0`, then
`fderiv ℝ (log ∘ F) x = (F x)⁻¹ • fderiv ℝ F x`.  This is the `fderiv`-of-`log` component of the
Γ tensorization assembly. -/
theorem fderiv_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (x : E) (hd : DifferentiableAt ℝ F x) (hx : F x ≠ 0) :
    fderiv ℝ (fun y => Real.log (F y)) x = (F x)⁻¹ • fderiv ℝ F x :=
  (hd.hasFDerivAt.log hx).fderiv

/-- **The abstract product tensorization of the Γ-form inequality.**  For a product measure
`μ ⊗ ν`, the Γ-form log-Sobolev inequality with the square of the sup-norm gradient is at most the
sum of the two factor inequalities.  This is the remaining measure-theoretic input of the
assembly: applying `GaussianLogSobolevGrad μ` and `GaussianLogSobolevGrad ν` to the marginal and the
normalised slices, with the weighted-measure Jensen bound on `‖fderiv (log ∘ F)‖² F`. -/
def GaussianLogSobolevGradProdStep : Prop :=
  ∀ (m n : ℕ), GaussianLogSobolevGrad m → GaussianLogSobolevGrad n →
    GaussianLogSobolevGrad (m + n)

/-- The Γ-form tensorization step follows from the one-dimensional inequality and the abstract
product step (which itself packages the `Measure.measurePreserving_piFinSuccAbove`
identification of `γ_{n+1}` with `γ_1 ⊗ γ_n`). -/
theorem gaussianLogSobolevGradTensorStep_of_prodStep
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep) :
    GaussianLogSobolevGradTensorStep := by
  intro n hn
  exact hprod n 1 hn hone

end LatticeProb
