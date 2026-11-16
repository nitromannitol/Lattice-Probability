import LatticeProb.Analysis.Schauder.Continuum
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Moving a derivative onto an integrable kernel

For an integrable differentiable kernel `K` with integrable directional derivatives and a bounded
function `g` with bounded continuous derivative, integration by parts transfers a derivative of `g`
onto `K` in the convolution-type integral `∫ K(y) g(x - y) dy`:
`∫ K(y) (Dg)(x - y) v dy = ∫ (DK)(y) v · g(x - y) dy`.
The two signs coming from `∂_v [y ↦ g (x - y)] = -(Dg)(x - y) v` and from integration by parts
cancel. This is the step that places a derivative on the heat kernel in the Schauder-free proof.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The directional derivative of the reflected translate `y ↦ g (x - y)` of a differentiable
function `g` is the negative of the directional derivative of `g` at `x - y`. -/
theorem fderiv_comp_sub_apply {g : Euc d → ℝ} (hg : Differentiable ℝ g) (x y v : Euc d) :
    fderiv ℝ (fun z => g (x - z)) y v = -(fderiv ℝ g (x - y) v) := by
  have h1 : HasFDerivAt (fun z : Euc d => x - z) (-(ContinuousLinearMap.id ℝ (Euc d))) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 : HasFDerivAt (fun z => g (x - z))
      ((fderiv ℝ g (x - y)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) y :=
    ((hg (x - y)).hasFDerivAt).comp y h1
  rw [h2.fderiv]
  simp

/-- **Integration by parts against a kernel.** A derivative of a bounded function `g` with bounded
continuous derivative can be moved onto an integrable differentiable kernel `K` with integrable
directional derivatives: `∫ K(y) (Dg)(x - y) v dy = ∫ (DK)(y) v · g(x - y) dy`. -/
theorem integral_mul_fderiv_comp_sub_eq {K g : Euc d → ℝ}
    (hK : Differentiable ℝ K) (hKi : Integrable K)
    (hK'i : ∀ v : Euc d, Integrable fun y => fderiv ℝ K y v)
    (hg : Differentiable ℝ g) (hgc : Continuous g) (hg'c : Continuous (fderiv ℝ g))
    {A B : ℝ} (hgA : ∀ y, |g y| ≤ A) (hgB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (x v : Euc d) :
    ∫ y, K y * fderiv ℝ g (x - y) v = ∫ y, fderiv ℝ K y v * g (x - y) := by
  have hsub : Continuous fun y : Euc d => x - y := continuous_const.sub continuous_id
  have hGd : Differentiable ℝ fun y : Euc d => g (x - y) := by
    intro y
    exact ((hg (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)).differentiableAt
  have hGm : AEStronglyMeasurable (fun y : Euc d => g (x - y)) volume :=
    (hgc.comp hsub).aestronglyMeasurable
  have hGb : ∀ᵐ y : Euc d ∂volume, ‖g (x - y)‖ ≤ A :=
    Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgA (x - y)
  have hDm : AEStronglyMeasurable (fun y : Euc d => fderiv ℝ g (x - y) v) volume :=
    ((hg'c.comp hsub).clm_apply continuous_const).aestronglyMeasurable
  have hDb : ∀ᵐ y : Euc d ∂volume, ‖fderiv ℝ g (x - y) v‖ ≤ B * ‖v‖ :=
    Filter.Eventually.of_forall fun y =>
      ((fderiv ℝ g (x - y)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hgB (x - y)) (norm_nonneg v))
  have hf'g : Integrable (fun y : Euc d => fderiv ℝ K y v * g (x - y)) volume :=
    (hK'i v).mul_bdd hGm hGb
  have hfg : Integrable (fun y : Euc d => K y * g (x - y)) volume :=
    hKi.mul_bdd hGm hGb
  have hfg' : Integrable (fun y : Euc d => K y * fderiv ℝ (fun z => g (x - z)) y v) volume := by
    simp_rw [fderiv_comp_sub_apply hg x _ v, mul_neg]
    exact (hKi.mul_bdd hDm hDb).neg
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v)
    hf'g hfg' hfg (fun y _ => hK y) (fun y _ => hGd y)
  simp_rw [fderiv_comp_sub_apply hg x _ v, mul_neg, integral_neg] at key
  exact neg_inj.mp key

end

end LatticeProb.Analysis.Schauder
