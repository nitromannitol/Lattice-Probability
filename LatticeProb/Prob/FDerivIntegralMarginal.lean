/-
# Differentiation under the integral for a marginal

The Leibniz rule for the marginal `F x = ∫ y, h(x,y) dν(y)` of a function
`h : V × β → ℝ`: under a uniform integrable bound on `‖fderiv h‖`, the marginal
is differentiable with derivative the integral of the slice derivatives,

  `fderiv ℝ F x = ∫ y, fderiv ℝ (fun x => h(x,y)) x dν(y)`.

This is the missing declaration named in
`~/fleet/audit/lib-gaussianlogsobolev-gradtensor.md` §3; it is the last input of
the slicewise Jensen step of the Γ-form Gaussian log-Sobolev tensorization.  The
proof is Mathlib's parametric differentiation lemma
`hasFDerivAt_integral_of_dominated_of_fderiv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean:210`).
-/
import Mathlib

noncomputable section

open MeasureTheory
open scoped Topology

namespace LatticeProb

/-- The derivative of a slice is the composition of the joint derivative with the
inclusion of the first factor. -/
theorem fderiv_slice {V β : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup β] [NormedSpace ℝ β] (h : V × β → ℝ) (a : β) (x : V)
    (hd : DifferentiableAt ℝ h (x, a)) :
    fderiv ℝ (fun x => h (x, a)) x
      = (fderiv ℝ h (x, a)).comp (ContinuousLinearMap.inl ℝ V β) := by
  have hchain : HasFDerivAt (fun y : V => h (y, a))
      ((fderiv ℝ h (x, a)).comp (ContinuousLinearMap.inl ℝ V β)) x :=
    HasFDerivAt.comp (x := x) (f := fun y : V => (y, a))
      (g := h) (g' := fderiv ℝ h (x, a)) (f' := ContinuousLinearMap.inl ℝ V β)
      hd.hasFDerivAt (hasFDerivAt_prodMk_left x a)
  exact hchain.fderiv

/-- **Differentiation under the integral for a marginal.**  If `h : V × β → ℝ` is
`C¹`, the slice `h(x, ·)` is `ν`-integrable at the base point `x`, `‖fderiv h‖` is
dominated by an integrable function of the second coordinate, and the slices and
their derivatives are a.e. strongly measurable, then the marginal
`F x = ∫ y, h(x,y) dν(y)` is differentiable at `x` with derivative the integral of
the slice derivatives. -/
theorem hasFDerivAt_integral_marginal {V β : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β]
    (ν : Measure β) (h : V × β → ℝ) (x : V)
    (hC : ContDiff ℝ 1 h) (hint : Integrable (fun a => h (x, a)) ν)
    (bound : β → ℝ) (hbound_int : Integrable bound ν)
    (hbound : ∀ p : V × β, ‖fderiv ℝ h p‖ ≤ bound p.2)
    (hF_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun a => h (x', a)) ν)
    (hF'_meas : AEStronglyMeasurable
      (fun a => (fderiv ℝ h (x, a)).comp (ContinuousLinearMap.inl ℝ V β)) ν) :
    HasFDerivAt (fun x => ∫ a, h (x, a) ∂ν)
      (∫ a, (fderiv ℝ h (x, a)).comp (ContinuousLinearMap.inl ℝ V β) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (s := Set.univ)
    (F := fun x a => h (x, a))
    (F' := fun x a => (fderiv ℝ h (x, a)).comp (ContinuousLinearMap.inl ℝ V β))
    (x₀ := x) (bound := bound) Filter.univ_mem hF_meas hint hF'_meas ?_ hbound_int ?_
  · filter_upwards with a
    intro x' _
    calc ‖(fderiv ℝ h (x', a)).comp (ContinuousLinearMap.inl ℝ V β)‖
        ≤ ‖fderiv ℝ h (x', a)‖ * ‖ContinuousLinearMap.inl ℝ V β‖ :=
          ContinuousLinearMap.opNorm_comp_le (h := fderiv ℝ h (x', a))
            (ContinuousLinearMap.inl ℝ V β)
      _ ≤ ‖fderiv ℝ h (x', a)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ V β) (norm_nonneg _)
      _ = ‖fderiv ℝ h (x', a)‖ := mul_one _
      _ ≤ bound a := hbound (x', a)
  · filter_upwards with a
    intro x' _
    have hd : DifferentiableAt ℝ h (x', a) :=
      (hC.contDiffAt (x := (x', a))).differentiableAt one_ne_zero
    have hchain : HasFDerivAt (fun y : V => h (y, a))
        ((fderiv ℝ h (x', a)).comp (ContinuousLinearMap.inl ℝ V β)) x' :=
      HasFDerivAt.comp (x := x') (f := fun y : V => (y, a))
        (g := h) (g' := fderiv ℝ h (x', a)) (f' := ContinuousLinearMap.inl ℝ V β)
        hd.hasFDerivAt (hasFDerivAt_prodMk_left x' a)
    exact hchain

end LatticeProb
