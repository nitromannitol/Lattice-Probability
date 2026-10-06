/-
# The exponential form of the one-dimensional Γ-form Gaussian log-Sobolev inequality

`GaussianLogSobolevGradOne := GaussianLogSobolevGrad 1` (`GaussianLogSobolevOneInput.lean`) is the
one-dimensional Γ-form Gaussian log-Sobolev inequality.  This module reduces it to the standard
**exponential** (Gross) form

  `∫ e^φ · φ dγ ≤ (1/2) ∫ ‖∇ φ‖² e^φ dγ`  for `∫ e^φ dγ = 1`,

by the log/exp change of variables `h = e^φ` (`φ = log ∘ h`).  Both directions are proved, so the
two predicates are equivalent; the exponential form is the exact missing Mathlib declaration.

* `gaussianLogSobolevGradOneExp_of_grad` — Γ-form ⇒ exponential form;
* `gaussianLogSobolevGrad_of_oneExp` — exponential form ⇒ Γ-form;
* `gaussianLogSobolevGrad_one_iff_exp` — the equivalence.
-/
import LatticeProb.Prob.GaussianLogSobolevOneInput

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The one-dimensional Γ-form Gaussian log-Sobolev inequality in exponential form.**  For a
`C¹` exponent `φ` with `∫ e^φ dγ₁ = 1`, `∫ e^φ · φ dγ₁ ≤ (1/2) ∫ ‖∇ φ‖² e^φ dγ₁`. -/
def GaussianLogSobolevGradOneExp : Prop :=
  ∀ φ : (Fin 1 → ℝ) → ℝ, ContDiff ℝ 1 φ →
    Integrable (fun x => Real.exp (φ x)) (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => Real.exp (φ x) * φ x)
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    Integrable (fun x => ‖fderiv ℝ φ x‖ ^ 2 * Real.exp (φ x))
      (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) →
    (∫ x, Real.exp (φ x) ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1) = 1) →
    (∫ x, Real.exp (φ x) * φ x ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, ‖fderiv ℝ φ x‖ ^ 2 * Real.exp (φ x)
          ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)

/-- The exponential form follows from the Γ-form by `h = e^φ`: `log ∘ exp = id`, so the Γ-form
applied to `h = e^φ` is literally the exponential inequality. -/
theorem gaussianLogSobolevGradOneExp_of_grad (hgrad : GaussianLogSobolevGrad 1) :
    GaussianLogSobolevGradOneExp := by
  intro φ hφ hint hintlog hgradint hnorm
  have hfun : (fun y : Fin 1 → ℝ => Real.log (Real.exp (φ y))) = φ :=
    funext fun y => Real.log_exp (φ y)
  have key := hgrad (fun x => Real.exp (φ x)) (fun x => Real.exp_pos _) hφ.exp hint
    (by simpa only [Real.log_exp] using hintlog)
    (by rw [hfun]; exact hgradint)
    hnorm
  simpa only [hfun, Real.log_exp] using key

/-- The Γ-form follows from the exponential form by `φ = log ∘ h`: on the support of a positive `h`
the logarithm is `C¹`, and `exp ∘ log = id`. -/
theorem gaussianLogSobolevGrad_of_oneExp (hexp : GaussianLogSobolevGradOneExp) :
    GaussianLogSobolevGrad 1 := by
  intro h hpos hcont hint hintlog hgradint hnorm
  have hphi : ContDiff ℝ 1 (fun x => Real.log (h x)) :=
    contDiff_iff_contDiffAt.mpr fun x => (hcont.contDiffAt).log (ne_of_gt (hpos x))
  have hexpfun : (fun x : Fin 1 → ℝ => Real.exp (Real.log (h x))) = h :=
    funext fun x => Real.exp_log (hpos x)
  have hprod : (fun x : Fin 1 → ℝ => Real.exp (Real.log (h x)) * Real.log (h x)) =
      fun x => h x * Real.log (h x) :=
    funext fun x => by rw [Real.exp_log (hpos x)]
  have hgr : (fun x : Fin 1 → ℝ =>
        ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * Real.exp (Real.log (h x))) =
      fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x :=
    funext fun x => by rw [Real.exp_log (hpos x)]
  have key := hexp (fun x => Real.log (h x)) hphi
    (by rw [hexpfun]; exact hint)
    (by rw [hprod]; exact hintlog)
    (by rw [hgr]; exact hgradint)
    (by rw [hexpfun]; exact hnorm)
  simpa only [hprod, hgr] using key

/-- **The Γ-form and the exponential form are equivalent.**  This pins the one-dimensional
Gaussian log-Sobolev input to its standard (Gross) exponential statement. -/
theorem gaussianLogSobolevGrad_one_iff_exp :
    GaussianLogSobolevGrad 1 ↔ GaussianLogSobolevGradOneExp :=
  ⟨gaussianLogSobolevGradOneExp_of_grad, gaussianLogSobolevGrad_of_oneExp⟩

end LatticeProb
