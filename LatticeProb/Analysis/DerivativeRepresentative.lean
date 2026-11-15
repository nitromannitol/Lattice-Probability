import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Classical derivatives of almost-everywhere representatives -/

set_option autoImplicit false

open Filter MeasureTheory Set Topology

namespace LatticeProb

/-- Differentiable representatives that agree almost everywhere on an open set
have equal derivatives there, for any measure positive on nonempty open sets. -/
theorem eqOn_derivative_of_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℝ} [Measure.IsOpenPosMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    {f g f' g' : ℝ → F} (hfg : f =ᵐ[μ.restrict U] g)
    (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ U, HasDerivAt g (g' x) x) : EqOn f' g' U := by
  have hfc : ContinuousOn f U := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g U := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have heq : EqOn f g U := Measure.eqOn_open_of_ae_eq hfg hU hfc hgc
  intro x hx
  have hnear : g =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (heq hy).symm
  exact ((hf x hx).congr_of_eventuallyEq hnear).unique (hg x hx)

/-- The derivative representatives also agree almost everywhere on the set. -/
theorem ae_eq_derivative_of_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure ℝ} [Measure.IsOpenPosMeasure μ] {U : Set ℝ} (hU : IsOpen U)
    {f g f' g' : ℝ → F} (hfg : f =ᵐ[μ.restrict U] g)
    (hf : ∀ x ∈ U, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ U, HasDerivAt g (g' x) x) : f' =ᵐ[μ.restrict U] g' := by
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact eqOn_derivative_of_ae_eq hU hfg hf hg hx

end LatticeProb
