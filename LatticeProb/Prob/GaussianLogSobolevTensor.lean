/-
# Tensorization of the Gaussian log-Sobolev inequality: reduction and gap

`LatticeProb.GaussianLogSobolev n` is the Gaussian log-Sobolev inequality for
the standard product law `γ_n = Measure.pi (fun _ : Fin n => gaussianReal 0 1)`:
for a positive `h` with `∫ h ∂γ_n = 1` whose logarithm is `C`-Lipschitz,
`∫ h log h ∂γ_n ≤ C² / 2`.  Only the degenerate `n = 0` case is proved
(`gaussianLogSobolev_zero`).

This module records the two-step route to all `n`:

* `GaussianLogSobolevTensorStep` — the one-step tensorization `n → n + 1`; and
* `GaussianLogSobolevOne` — the one-dimensional Gaussian log-Sobolev inequality.

Given both, `gaussianLogSobolev_of_one_of_tensorStep` produces every `n` by
induction, and `gaussianHerbstBound_of_one_of_tensorStep` pushes that through the
completed Herbst chain (`gaussianHerbstBound_of_logSobolev`) to the exponential
moment bound consumed by `gaussian_lipschitz_concentration`.

## The obstruction to the tensorization step

The tensorization of the *sharp* log-Sobolev inequality is genuine but cannot be
derived from the frozen Lipschitz form `GaussianLogSobolev` alone.  Splitting
`Ent_{μ⊗ν}(h) = ∫ Ent_ν(h_x) dμ_x + Ent_μ(F)`, `F x = ∫ h(x,·) dν`, and applying
the Lipschitz-form inequality to each factor bounds the entropy by

  `(C_x² + C_y²) / 2`,   `C_x = sup_x ‖∇_x log h‖₁`,  `C_y = sup_y ‖∇_y log h‖₁`,

whereas the joint sup-metric Lipschitz constant is
`C = sup(‖∇_x log h‖₁ + ‖∇_y log h‖₁)`.  The supremum of the sum can be strictly
smaller than the sum of the suprema (the gradient direction rotates), so
`C_x² + C_y²` can be twice `C²`: a factor-2 loss that misses the required `C²/2`.

The sharp tensorization is instead the one for the *gradient* (carré-du-champ)
form of the inequality, `Ent_ν(g) ≤ (1/2) ∫ |∇ log g|² g dν`: there the two
Gaussian factors contribute `|∇_x log h|²` and `|∇_y log h|²`, whose sum is
controlled by the joint gradient via Jensen, and the constant is preserved.
The exact missing Mathlib declaration is therefore the one-dimensional
gradient-form Gaussian log-Sobolev inequality (Gross/Bakry–Émery), from which
`GaussianLogSobolevOne` follows by `|∇ log h| ≤ C`.
-/
import LatticeProb.External.GaussianLogSobolev
import LatticeProb.Prob.HerbstFromLSI

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- The one-dimensional Gaussian log-Sobolev inequality, `GaussianLogSobolev 1`.
This is Gross's inequality for the standard Gaussian on the line; it is the
analytic input of the tensorization and is not available in Mathlib. -/
def GaussianLogSobolevOne : Prop :=
  GaussianLogSobolev 1

/-- The one-step tensorization of the Gaussian log-Sobolev inequality: the
sharp inequality for the product of `n` standard Gaussians implies it for the
product of `n + 1`. -/
def GaussianLogSobolevTensorStep : Prop :=
  ∀ n : ℕ, GaussianLogSobolev n → GaussianLogSobolev (n + 1)

/-- The one-dimensional Gaussian log-Sobolev inequality and the tensorization
step together give the inequality in every dimension, by induction. -/
theorem gaussianLogSobolev_succ_of_one
    (hone : GaussianLogSobolevOne) (hstep : GaussianLogSobolevTensorStep) :
    ∀ n : ℕ, GaussianLogSobolev (n + 1) := by
  intro n
  induction n with
  | zero => exact hone
  | succ n ih => exact hstep (n + 1) ih

/-- The tensorization form named in the packet, with the dimension explicit. -/
theorem gaussianLogSobolev_succ_of_one_apply
    (hone : GaussianLogSobolevOne) (hstep : GaussianLogSobolevTensorStep) (n : ℕ) :
    GaussianLogSobolev (n + 1) :=
  gaussianLogSobolev_succ_of_one hone hstep n

/-- The one-dimensional Gaussian log-Sobolev inequality and the tensorization
step together give the inequality in every dimension. -/
theorem gaussianLogSobolev_of_one_of_tensorStep
    (hone : GaussianLogSobolevOne) (hstep : GaussianLogSobolevTensorStep) :
    ∀ n : ℕ, GaussianLogSobolev n := by
  intro n
  cases n with
  | zero => exact gaussianLogSobolev_zero
  | succ n => exact gaussianLogSobolev_succ_of_one hone hstep n

/-- Consequently the Herbst exponential moment bound holds in every dimension,
through the completed Herbst chain `gaussianHerbstBound_of_logSobolev`. -/
theorem gaussianHerbstBound_of_one_of_tensorStep
    (hone : GaussianLogSobolevOne) (hstep : GaussianLogSobolevTensorStep) (n : ℕ) :
    GaussianHerbstBound n :=
  gaussianHerbstBound_of_logSobolev n (gaussianLogSobolev_of_one_of_tensorStep hone hstep n)

end LatticeProb
