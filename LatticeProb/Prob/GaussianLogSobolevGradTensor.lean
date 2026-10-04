/-
# The entropy chain rule for a product measure

This is step (1) of the Γ-form tensorization recorded in
`~/fleet/audit/lib-gaussianlogsobolev-grad.md` §4: the entropy of a function on
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
`γ_{n+1}` with `γ_n ⊗ γ_1`.  Neither the Jensen bound (a differentiation-under-
the-integral plus vector-valued Jensen statement) nor its assembly is in Mathlib;
the residual stays the named `Prop` `GaussianLogSobolevGradTensorStep`.
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

end LatticeProb
