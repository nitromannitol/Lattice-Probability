/-
# The gradient (carré-du-champ) form of Gaussian log-Sobolev

`LatticeProb.GaussianLogSobolev n` is the frozen Gaussian log-Sobolev inequality
in *Lipschitz* form: a positive `h` with `∫ h ∂γ_n = 1` and `C`-Lipschitz
`log ∘ h` satisfies `∫ h log h ∂γ_n ≤ C² / 2`.  As recorded in
`~/fleet/audit/lib-gaussianlogsobolev-tensor.md`, that form does not tensorize
sharply: splitting the entropy over a product and applying the Lipschitz form to
the two factors loses a factor of two, because the sup of the sum of the two
coordinate l¹-gradient norms can be smaller than the sum of the two suprema.

The correct target is the **gradient** (Γ, carré-du-champ) form

  `∫ h log h ∂γ_n ≤ (1 / 2) ∫ ‖∇ (log ∘ h)‖² · h ∂γ_n`,

which *does* tensorize with the same constant: the two factors contribute
`‖∇_x log h‖²` and `‖∇_y log h‖²`, whose sum is controlled by the joint gradient
through Jensen.  This module makes that target machine-checked:

* `GaussianLogSobolevGrad n` — the Γ-form predicate for `C¹` densities;
* `GaussianLogSobolevGradTensorStep` — the one-step tensorization, isolated as a
  named `Prop`, with the reduction `(Γ 1-D) + (tensor step) ⇒ all n`;
* `gaussianLogSobolev_of_grad_smooth` — the Lipschitz form follows from the
  Γ form *for `C¹` densities*: `LipschitzWith C (log ∘ h)` gives
  `‖fderiv (log ∘ h) x‖ ≤ C` everywhere, hence the Γ bound is at most `C² / 2`.

The passage from the frozen predicate to the `C¹` hypotheses is the honest
regularity gap: the frozen form quantifies over *all* positive `C`-Lipschitz-log
`h`, while the Γ form is stated for `C¹` densities.  Extending the Γ bound to
merely Lipschitz-log densities needs a higher-dimensional Rademacher theorem
(the Dirichlet energy of a Lipschitz function) and a density/mollification
argument, neither of which is in Mathlib; the one-dimensional Rademacher theorem
`LipschitzWith.ae_differentiableAt_real` exists, but there is no
`Fin n → ℝ` analogue.  The exact missing declaration is recorded at the end of
this file.
-/
import LatticeProb.Prob.GaussianLogSobolevTensor
import LatticeProb.External.GaussianLogSobolev

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The gradient (carré-du-champ) form of the Gaussian log-Sobolev
inequality.**  For a positive `C¹` density `h` on `Fin n → ℝ` with `∫ h ∂γ_n = 1`
whose weighted squared gradient is integrable,

  `∫ h log h ∂γ_n ≤ (1 / 2) ∫ ‖∇ (log ∘ h)‖² · h ∂γ_n`.

This is the sharp form that tensorizes; it implies the frozen Lipschitz form
(for `C¹` densities) and is not derivable from it. -/
def GaussianLogSobolevGrad (n : ℕ) : Prop :=
  ∀ h : (Fin n → ℝ) → ℝ, (∀ x, 0 < h x) → ContDiff ℝ 1 h →
    Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) →
    (∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) →
    (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)

/-- The one-step tensorization of the gradient form: the sharp Γ-form inequality
for the product of `n` standard Gaussians implies it for the product of `n + 1`.
This is the step whose Lipschitz-form analogue fails with a factor of two. -/
def GaussianLogSobolevGradTensorStep : Prop :=
  ∀ n : ℕ, GaussianLogSobolevGrad n → GaussianLogSobolevGrad (n + 1)

/-- The one-dimensional gradient form and the tensorization step give the
gradient form in every dimension, by induction. -/
theorem gaussianLogSobolevGrad_of_one_of_tensorStep
    (hone : GaussianLogSobolevGrad 1) (hstep : GaussianLogSobolevGradTensorStep) :
    ∀ n : ℕ, GaussianLogSobolevGrad (n + 1) := by
  intro n
  induction n with
  | zero => exact hone
  | succ n ih => exact hstep (n + 1) ih

/-- **Lipschitz form from the gradient form, for `C¹` densities.**  If `log ∘ h`
is `C`-Lipschitz then `‖fderiv (log ∘ h) x‖ ≤ C` at every point, so the
`h`-weighted squared gradient is at most `C² ∫ h = C²`, and the Γ-form bound
gives the frozen conclusion `∫ h log h ≤ C² / 2`. -/
theorem gaussianLogSobolev_of_grad_smooth {n : ℕ} (hgrad : GaussianLogSobolevGrad n)
    (h : (Fin n → ℝ) → ℝ) (hpos : ∀ x, 0 < h x) (hsmooth : ContDiff ℝ 1 h)
    (hint : Integrable h (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hlog : Integrable (fun x => h x * Real.log (h x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hgradint : Integrable (fun x => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1))
    (hnorm : ∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1)
    (C : NNReal) (hC : LipschitzWith C (fun x => Real.log (h x))) :
    (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ (C : ℝ) ^ 2 / 2 := by
  have hgradbound := hgrad h hpos hsmooth hint hlog hgradint hnorm
  have hpoint : ∀ x : Fin n → ℝ,
      ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x ≤ (C : ℝ) ^ 2 * h x := by
    intro x
    have hle : ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ≤ (C : ℝ) :=
      norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hC
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hpos x).le
  have hintC : Integrable (fun x => (C : ℝ) ^ 2 * h x)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := hint.const_mul _
  have hbound : ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤ (C : ℝ) ^ 2 := by
    calc ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        ≤ ∫ x, (C : ℝ) ^ 2 * h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hpos x).le)
            hintC (Filter.Eventually.of_forall hpoint)
      _ = (C : ℝ) ^ 2 * ∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
          integral_const_mul _ _
      _ = (C : ℝ) ^ 2 := by rw [hnorm, mul_one]
  calc (∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      ≤ (1 / 2) * ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := hgradbound
    _ ≤ (1 / 2) * (C : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (C : ℝ) ^ 2 / 2 := by ring

/-! ### The exact missing Mathlib declaration

The passage from the frozen Lipschitz form to the gradient form requires
regularising a `C`-Lipschitz-log density `h` that is not `C¹`.  The missing
Mathlib input is the higher-dimensional Rademacher theorem together with the
identification of the `h`-weighted Dirichlet energy with the limit of the
squared gradients of a mollification:

```lean
theorem lipschitzWith_ae_fderiv_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {C : NNReal}
    (hf : LipschitzWith C f) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      HasFDerivAt f (fderiv ℝ f x) x ∧ ‖fderiv ℝ f x‖ ≤ C

theorem integral_fderiv_sq_mollify_tendsto {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith C f) :
    Tendsto (fun ε => ∫ x, ‖fderiv ℝ (f ⋆ ρ ε) x‖ ^ 2 * w x) (𝓝[>] 0)
      (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 * w x))
```

The one-dimensional case of the first is
`LipschitzWith.ae_differentiableAt_real` (`Mathlib/Analysis/BoundedVariation.lean`);
there is no `Fin n → ℝ` analogue in Mathlib.  With these, `GaussianLogSobolev n`
follows from `GaussianLogSobolevGrad n` for all positive `C`-Lipschitz-log `h`.  The
second missing input is the Γ-form tensorization
`GaussianLogSobolevGradTensorStep`, whose proof needs the entropy chain rule
`Ent_{μ⊗ν}(h) = ∫ Ent_ν(h_x) dμ + Ent_μ(F)` together with the Jensen bound
`‖∇_x log F‖² F ≤ ∫ ‖∇_x log h‖² h_x dν`; Mathlib has the chain rule
(`InformationTheory.klDiv_compProd_eq_add`) but not the assembled Γ tensorization. -/

end LatticeProb
