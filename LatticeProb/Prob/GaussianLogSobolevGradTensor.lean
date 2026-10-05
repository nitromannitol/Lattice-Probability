/-
# The entropy chain rule for a product measure

This is step (1) of the Γ-form tensorization (see `GaussianLogSobolevGrad.lean`):
the entropy of a function on
a product `μ ⊗ ν` splits as the average of the slice entropies plus the entropy
of the marginal,

  `Ent_{μ⊗ν}(h) = ∫ x, Ent_ν(h(x,·)) dμ(x) + Ent_μ(F x)`,
  `F x = ∫ y, h(x,y) dν(y)`.

The proof is Fubini together with the elementary splitting
`Ent_ρ(g) = ∫ g log g dρ - (∫ g dρ) log (∫ g dρ)`.

## The remaining steps for the Γ tensorization

With the split in hand, the Γ tensorization needs (2) the slicewise Jensen bound
`‖∇_x log F‖² · F ≤ ∫ ‖∇_x log h‖² · h_x dν`, so that the two factors contribute
`∫ ‖∇ log h‖² h` with the constant preserved, and then (3) the identification of
`γ_{n+1}` with `γ_n ⊗ γ_1`.

The vector-valued Jensen half of (2) is proved below as
`norm_sq_integral_le_integral_norm_sq`: for a probability measure and a Bochner
integrable `g`, `‖∫ g dμ‖² ≤ ∫ ‖g‖² dμ`.  Applied to the probability measure
`(h_x / F x) · ν` and the field `y ↦ fderiv (log ∘ h(·,y)) x`, this gives the
slicewise bound once the marginal Leibniz rule identifies `fderiv (log ∘ F) x`
with the conditional average of `fderiv (log ∘ h(·,y)) x`; that differentiation
under the integral is the residual.  The assembly (3) then stays the named `Prop`
`GaussianLogSobolevGradTensorStep`.
-/
import LatticeProb.Prob.GaussianLogSobolevGrad

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
Jensen inequality for the convex function `t ↦ t²`.  This is the slicewise Jensen
step of the Γ tensorization, applied to the probability measure `h_x / F x · ν`. -/
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

end LatticeProb
