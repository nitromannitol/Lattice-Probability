/-
# The regularity bridge for the general-`n` Gaussian log-Sobolev composition

`LatticeProb/Prob/GaussianLogSobolevGeneral.lean` reduces the general-`n` Gaussian
log-Sobolev and Herbst bounds to the Γ-form chain plus the named **regularity
bridge**

  `GaussianLogSobolevGradToLipschitz n : Prop := GaussianLogSobolevGrad n → GaussianLogSobolev n`,

the passage from the `C¹` densities of the Γ-form predicate to the merely
Lipschitz-log densities of the frozen predicate.  This file reduces that bridge to
a single explicit approximation statement and proves the composition.

## The chain

The Γ-form inequality holds for `C¹` densities (`gaussianLogSobolev_of_grad_smooth`
in `GaussianLogSobolevGrad.lean`).  To reach an arbitrary positive `h` whose
logarithm is `C`-Lipschitz, it suffices to approximate `h` by `C¹` densities with
the *same* Lipschitz-log constant, preserving the normalisation and converging in
entropy.  That approximation is stated as `LipschitzLogApprox n`, and the bridge
and the general-`n` composition then follow by a limit.

## The exact missing declaration

`LipschitzLogApprox n`: a positive density on `Fin n → ℝ` with `C`-Lipschitz
logarithm is the entropy limit of a sequence of `C¹` positive densities with the
same `C`-Lipschitz logarithm and the same total mass.  Its construction is a
mollification: `h ⋆ ρ_k` is `C¹` and positive, `∫ h ⋆ ρ_k = ∫ h`, and the
log-sum-exp contraction `log (E[e^{f}])` is `C`-Lipschitz whenever `f` is, so the
Lipschitz constant is preserved; the entropy convergence is the standard
lower-semicontinuity of `t log t` plus the mollification limit.  Neither the
higher-dimensional Rademacher theorem (`LipschitzWith.ae_differentiableAt_real`
exists only for `ℝ → V`) nor the convolution machinery for a general positive
density is in Mathlib.
-/
import LatticeProb.Prob.GaussianLogSobolevGeneral

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- **The mollification input of the regularity bridge.**  A positive density on
`Fin n → ℝ` whose logarithm is `C`-Lipschitz is the entropy limit of a sequence of
`C¹` positive densities with the same `C`-Lipschitz logarithm, the same total mass
`1`, and the gradient integrability the Γ-form predicate consumes. -/
def LipschitzLogApprox (n : ℕ) : Prop :=
  ∀ (h : (Fin n → ℝ) → ℝ) (C : NNReal),
    (∀ x, 0 < h x) →
    LipschitzWith C (fun x => Real.log (h x)) →
    Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) →
      ∃ hε : ℕ → (Fin n → ℝ) → ℝ,
        (∀ k, (∀ x, 0 < hε k x) ∧ ContDiff ℝ 1 (hε k) ∧
          LipschitzWith C (fun x => Real.log (hε k x)) ∧
          Integrable (hε k) (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          Integrable (fun x => hε k x * Real.log (hε k x))
            (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (hε k y)) x‖ ^ 2 * hε k x)
            (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
          (∫ x, hε k x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1)) ∧
        Tendsto (fun k => ∫ x, hε k x * Real.log (hε k x)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) atTop
          (𝓝 (∫ x, h x * Real.log (h x)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))

/-- **The regularity bridge from the mollification input.**  If the one-step
Γ-form inequality `GaussianLogSobolevGrad n` holds and the mollification input
`LipschitzLogApprox n` is available, then the frozen Lipschitz form
`GaussianLogSobolev n` holds: apply the Γ-form bound to each approximant (the `C¹`
case `gaussianLogSobolev_of_grad_smooth`) and pass to the entropy limit. -/
theorem gaussianLogSobolevGradToLipschitz_of_approx {n : ℕ}
    (hgrad : GaussianLogSobolevGrad n) (happ : LipschitzLogApprox n) :
    GaussianLogSobolevGradToLipschitz n := by
  intro hgrad' h hpos hint hlog hnorm C hlip
  obtain ⟨hε, hprops, htend⟩ := happ h C hpos hlip hint hlog hnorm
  have hle : ∀ k, (∫ x, hε k x * Real.log (hε k x)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ≤ (C : ℝ) ^ 2 / 2 := by
    intro k
    obtain ⟨hp, hc, hlc, hi, hli, hgi, hnk⟩ := hprops k
    exact gaussianLogSobolev_of_grad_smooth (n := n) hgrad (hε k) hp hc hi hli hgi hnk C hlc
  exact le_of_tendsto' htend hle

/-- **The frozen Gaussian log-Sobolev inequality in every dimension, from the
mollification input.**  This replaces the hypothesis `∀ n, GaussianLogSobolevGradToLipschitz n`
of `gaussianLogSobolev_all_of_one_of_prodStep` by the Γ-form hypotheses and the single
mollification input. -/
theorem gaussianLogSobolev_all_of_one_of_prodStep_of_approx
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep)
    (happ : ∀ n : ℕ, LipschitzLogApprox n) :
    ∀ n : ℕ, GaussianLogSobolev n := by
  intro n
  cases n with
  | zero => exact gaussianLogSobolev_zero
  | succ n =>
      exact gaussianLogSobolevGradToLipschitz_of_approx (n := n + 1)
        (gaussianLogSobolevGrad_all_of_one_of_prodStep hone hprod n) (happ (n + 1))
        (gaussianLogSobolevGrad_all_of_one_of_prodStep hone hprod n)

/-- **The Herbst exponential moment bound in every dimension, from the
mollification input.** -/
theorem gaussianHerbstBound_all_of_one_of_prodStep_of_approx
    (hone : GaussianLogSobolevGrad 1) (hprod : GaussianLogSobolevGradProdStep)
    (happ : ∀ n : ℕ, LipschitzLogApprox n) (n : ℕ) :
    GaussianHerbstBound n :=
  gaussianHerbstBound_of_logSobolev n
    (gaussianLogSobolev_all_of_one_of_prodStep_of_approx hone hprod happ n)

end LatticeProb
