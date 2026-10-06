/-
# The Gaussian log-Sobolev inequality in every dimension: the assembly and its residual

`LatticeProb.GaussianLogSobolev n` (`LatticeProb/External/GaussianLogSobolev.lean`) is the cited
Gaussian log-Sobolev inequality on `γ_n = Measure.pi (fun _ : Fin n => gaussianReal 0 1)`, in the
Herbst (Lipschitz-log) form.  This module is the assembly: it collects the landed chain into a
single statement and names the residual exactly.

## The chain, and what each step consumes

1. `GaussianLogSobolevGrad 1` — the one-dimensional **Γ-form** (carré-du-champ) inequality
   `∫ h log h ∂γ₁ ≤ (1/2) ∫ ‖∇ (log ∘ h)‖² h ∂γ₁` for positive `C¹` `h` with `∫ h ∂γ₁ = 1`.
   It is equivalent to the exponential (Gross) form (`gaussianLogSobolevGrad_one_iff_exp`) and
   follows from the Ornstein–Uhlenbeck heat-flow contraction
   (`gaussianLogSobolevGrad_of_ouFlow`).
2. `GaussianLogSobolevGradTensorStep` — the one-step tensorization
   `Grad n → Grad (n + 1)`.  Given (1) it is *equivalent* to the abstract product step
   `Grad m → Grad n → Grad (m + n)` (`gaussianLogSobolevGradProdStep_iff_tensorStep`), so the two
   formulations are interchangeable; neither follows from (1) alone.
3. `LipschitzLogApprox n` — the regularity bridge from the `C¹` densities of the Γ-form
   predicate to the merely Lipschitz-log densities of the frozen predicate.

Given (1), (2) and (3), `gaussianLogSobolev_all_of_residual` produces `GaussianLogSobolev n` for
every `n`, and `gaussianHerbstBound_all_of_residual` pushes it through the completed Herbst chain
to `GaussianHerbstBound n`.

## The residual, exactly

The residual is the triple `GaussianLogSobolevResidual` below: the one-dimensional heat-flow
contraction, the one-step tensorization, and the mollification input.  Each is a named `Prop`,
never an axiom, and each is consumed by exactly one step of the assembly.

## The regularity bridge

The input `LipschitzLogApprox n` requires smooth positive approximating densities with the same
Lipschitz bound on their logarithms, mass one, gradient integrability, and convergence of the
entropy integrals. This approximation input remains explicit in the assembly.
-/
import LatticeProb.Prob.GaussianLogSobolevRegularity
import LatticeProb.Prob.GaussianLogSobolevOUFlow
import LatticeProb.Prob.GaussianLogSobolevGradProd

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The residual of the general-`n` Gaussian log-Sobolev chain.**  The one-dimensional
Ornstein–Uhlenbeck heat-flow contraction (entropy dissipation plus convergence to equilibrium
along the Mehler semigroup), the one-step tensorization of the Γ-form inequality, and the
mollification input of the regularity bridge.  Each is a named `Prop`, never an axiom. -/
def GaussianLogSobolevResidual : Prop :=
  GaussianOUFlowContraction ∧ GaussianLogSobolevGradTensorStep ∧ (∀ n : ℕ, LipschitzLogApprox n)

/-- **The one-dimensional Γ-form inequality from the residual.**  The heat-flow half of the
residual gives `GaussianLogSobolevGrad 1` through `gaussianLogSobolevGrad_of_ouFlow`. -/
theorem gaussianLogSobolevGrad_one_of_residual (h : GaussianLogSobolevResidual) :
    GaussianLogSobolevGrad 1 :=
  gaussianLogSobolevGrad_of_ouFlow h.1

/-- **The frozen Gaussian log-Sobolev inequality in every dimension, from the residual.**  This is
the assembly: the residual supplies the one-dimensional Γ-form inequality, the one-step
tensorization and the mollification input, and the landed chain produces `GaussianLogSobolev n`
for every `n`. -/
theorem gaussianLogSobolev_all_of_residual (h : GaussianLogSobolevResidual) :
    ∀ n : ℕ, GaussianLogSobolev n :=
  gaussianLogSobolev_all_of_one_of_prodStep_of_approx
    (gaussianLogSobolevGrad_one_of_residual h)
    (gaussianLogSobolevGradProdStep_of_tensorStep (gaussianLogSobolevGrad_one_of_residual h) h.2.1)
    h.2.2

/-- **The Herbst exponential moment bound in every dimension, from the residual.** -/
theorem gaussianHerbstBound_all_of_residual (h : GaussianLogSobolevResidual) (n : ℕ) :
    GaussianHerbstBound n :=
  gaussianHerbstBound_all_of_one_of_prodStep_of_approx
    (gaussianLogSobolevGrad_one_of_residual h)
    (gaussianLogSobolevGradProdStep_of_tensorStep (gaussianLogSobolevGrad_one_of_residual h) h.2.1)
    h.2.2 n

end LatticeProb
