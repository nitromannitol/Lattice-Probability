/-
# Entropy of a product measure, squared Jensen, and the derivative of a logarithm

Three analytic facts about the entropy functional
`Ent_ρ(g) = ∫ g log g dρ - (∫ g dρ) log (∫ g dρ)` (`LatticeProb.entropy`):

* `LatticeProb.entropy_prod_split`: the entropy chain rule for a product measure,

    `Ent_{μ⊗ν}(h) = ∫ x, Ent_ν(h(x,·)) dμ(x) + Ent_μ(F)`,  `F x = ∫ y, h(x,y) dν(y)`,

  by Fubini and the splitting of `Ent_ρ(g)`;
* `LatticeProb.norm_sq_integral_le_integral_norm_sq`: for a probability measure and a Bochner
  integrable `g`, `‖∫ g dμ‖² ≤ ∫ ‖g‖² dμ`;
* `LatticeProb.fderiv_log`: `fderiv ℝ (log ∘ F) x = (F x)⁻¹ • fderiv ℝ F x` where `F` is
  differentiable at `x` and `F x ≠ 0`.
-/
import Mathlib

noncomputable section

open MeasureTheory

namespace LatticeProb

/-- The entropy `Ent_ρ(g) = ∫ g log g dρ - (∫ g dρ) log (∫ g dρ)` of a
nonnegative function `g` with respect to a measure `ρ`.  For `∫ g dρ = 1` this is
the usual `∫ g log g dρ` of the log-Sobolev inequality. -/
noncomputable def entropy {α : Type*} [MeasurableSpace α] (ρ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂ρ - (∫ x, g x ∂ρ) * Real.log (∫ x, g x ∂ρ)

/-- **Entropy chain rule for a product.**  For integrable `h`, `h log h`, and
marginal entropy integrand, the entropy of `h` on `μ ⊗ ν` is the `μ`-average of
the slice entropies plus the entropy of the marginal `F x = ∫ y, h(x,y) dν`. -/
theorem entropy_prod_split {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (h : α × β → ℝ)
    (hint : Integrable h (μ.prod ν))
    (hlog : Integrable (fun p : α × β => h p * Real.log (h p)) (μ.prod ν))
    (hFlog : Integrable (fun x : α => (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν)) μ) :
    entropy (μ.prod ν) h
      = (∫ x, entropy ν (fun y => h (x, y)) ∂μ)
        + entropy μ (fun x => ∫ y, h (x, y) ∂ν) := by
  have hInner : Integrable (fun x : α => ∫ y, h (x, y) * Real.log (h (x, y)) ∂ν) μ :=
    hlog.integral_prod_left
  have hFint : Integrable (fun x : α => ∫ y, h (x, y) ∂ν) μ := hint.integral_prod_left
  simp only [entropy]
  rw [integral_sub hInner hFlog, integral_prod _ hlog, integral_prod _ hint]
  ring

/-- **Squared Jensen for a probability measure.**  The square of the norm of a
Bochner integral is at most the integral of the squared norm, the vector-valued
Jensen inequality for the convex function `t ↦ t²`. -/
theorem norm_sq_integral_le_integral_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → E} (hg : Integrable g μ) (hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ) :
    ‖∫ x, g x ∂μ‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h1 : ‖∫ x, g x ∂μ‖ ≤ ∫ x, ‖g x‖ ∂μ := norm_integral_le_integral_norm g
  have hf : Integrable (fun x => ‖g x‖) μ := hg.norm
  have hmem : ∀ᵐ x ∂μ, (fun x => ‖g x‖) x ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun x => norm_nonneg _
  have hjensen : (∫ x, ‖g x‖ ∂μ) ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂μ :=
    ConvexOn.map_integral_le (s := Set.Ici (0 : ℝ)) (f := fun x => ‖g x‖)
      (g := fun t : ℝ => t ^ 2) (convexOn_pow 2) (by fun_prop) isClosed_Ici hmem hf
      (by simpa only [Function.comp_def] using hg2)
  calc ‖∫ x, g x ∂μ‖ ^ 2 ≤ (∫ x, ‖g x‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := hjensen

/-- The chain rule for the logarithm: if `F` is differentiable at `x` and `F x ≠ 0`, then
`fderiv ℝ (log ∘ F) x = (F x)⁻¹ • fderiv ℝ F x`. -/
theorem fderiv_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (x : E) (hd : DifferentiableAt ℝ F x) (hx : F x ≠ 0) :
    fderiv ℝ (fun y => Real.log (F y)) x = (F x)⁻¹ • fderiv ℝ F x :=
  (hd.hasFDerivAt.log hx).fderiv

end LatticeProb
