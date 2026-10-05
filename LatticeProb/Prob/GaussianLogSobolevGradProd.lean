/-
# The Γ-form product step is the one-step tensorization

`GaussianLogSobolevGradProdStep` (`GaussianLogSobolevGradTensorProved.lean`) is the abstract product
tensorization `Grad m → Grad n → Grad (m + n)` of the gradient-form Gaussian log-Sobolev
inequality.  This module shows it is **not** an independent input: once the one-dimensional
inequality `GaussianLogSobolevGrad 1` is available, the one-step tensorization
`GaussianLogSobolevGradTensorStep` already produces `Grad k` in every dimension `k ≥ 1`, so the
product step's conclusion holds without its two hypotheses.  Hence, given `Grad 1`, the product
step and the one-step step are equivalent, and the sole remaining dimension-specific input of the
general-`n` chain is `GaussianLogSobolevGrad 1` together with the one-step tensorization.

* `gaussianLogSobolevGrad_zero` — the singleton case `Grad 0`;
* `gaussianLogSobolevGradProdStep_of_tensorStep` — `Grad 1` and `GradTensorStep` imply
  `GradProdStep`;
* `gaussianLogSobolevGradProdStep_iff_tensorStep` — the equivalence for fixed `Grad 1`.
-/
import LatticeProb.Prob.GaussianLogSobolevGradTensorProved

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- **The singleton case of the gradient-form Gaussian log-Sobolev inequality.**  On `Fin 0 → ℝ`
the Gaussian product measure is a Dirac mass and the normalised density is identically `1`, so the
entropy and the weighted squared-gradient term both vanish. -/
theorem gaussianLogSobolevGrad_zero : GaussianLogSobolevGrad 0 := by
  intro h _hpos _hc _hint _hlog _hgradint hnorm
  haveI : Subsingleton (Fin 0 → ℝ) := inferInstance
  have h_eq : h = fun _ => h (fun _ => 0) :=
    funext (fun x => congrArg h (Subsingleton.elim x _))
  have h1 : ∫ y, h y ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) =
      h (fun _ => 0) := by
    rw [h_eq, MeasureTheory.integral_const]
    simp
  have hc : h (fun _ => 0) = 1 := by linarith [hnorm, h1]
  have hconst : ∀ x : Fin 0 → ℝ, h x = 1 := fun x => by rw [h_eq]; exact hc
  have hzero : ∫ x, h x * Real.log (h x)
      ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = 0 := by
    simp [hconst]
  have hlog0 : (fun y : Fin 0 → ℝ => Real.log (h y)) = fun _ => (0 : ℝ) := by
    funext y
    rw [hconst y, Real.log_one]
  have hgrad0 : ∫ x, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x
      ∂(Measure.pi fun _ : Fin 0 => gaussianReal 0 1) = 0 := by
    have hpt : ∀ x : Fin 0 → ℝ, ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x = 0 := by
      intro x
      rw [hlog0, hconst x]
      simp
    rw [show (fun x : Fin 0 → ℝ => ‖fderiv ℝ (fun y => Real.log (h y)) x‖ ^ 2 * h x)
        = fun _ => (0 : ℝ) from funext hpt]
    simp
  rw [hzero, hgrad0]
  norm_num

/-- **The product step follows from the one-step tensorization.**  Given `Grad 1`, the one-step
step already gives `Grad k` for every `k ≥ 1` (with `Grad 0` covering the remaining case), so the
conclusion `Grad (m + n)` of the abstract product step holds without using its two hypotheses. -/
theorem gaussianLogSobolevGradProdStep_of_tensorStep
    (hone : GaussianLogSobolevGrad 1) (hstep : GaussianLogSobolevGradTensorStep) :
    GaussianLogSobolevGradProdStep := by
  intro m n _hm _hn
  rcases eq_or_ne (m + n) 0 with h0 | h0
  · rw [h0]
    exact gaussianLogSobolevGrad_zero
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [hk]
    exact gaussianLogSobolevGrad_of_one_of_tensorStep hone hstep k

/-- **The product step and the one-step step are equivalent** once `Grad 1` is available.  The
forward direction is `gaussianLogSobolevGradTensorStep_of_prodStep`; the reverse is
`gaussianLogSobolevGradProdStep_of_tensorStep`. -/
theorem gaussianLogSobolevGradProdStep_iff_tensorStep (hone : GaussianLogSobolevGrad 1) :
    GaussianLogSobolevGradProdStep ↔ GaussianLogSobolevGradTensorStep :=
  ⟨gaussianLogSobolevGradTensorStep_of_prodStep hone,
    gaussianLogSobolevGradProdStep_of_tensorStep hone⟩

end LatticeProb
