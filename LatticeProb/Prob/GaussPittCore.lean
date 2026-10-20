/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/PittCore.lean.
-/
import LatticeProb.Prob.GaussSmoothBdd
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Positive correlation of smooth bounded functions under the standard Gaussian

Let `γ` be the standard Gaussian measure of a finite-dimensional real inner product space `E`.
For bounded `C¹` functions `F, G : E → ℝ` with bounded continuous gradients `F', G' : E → E`
such that `⟪F' x, G' y⟫ ≥ 0` for all `x, y`, the expectations satisfy
`E[F] E[G] ≤ E[F G]`.

The proof is a bridge from the covariance identity `LatticeProb.GaussConc.integral_mul_sub_eq_cov`:
its right-hand side is an integral over `θ ∈ [0, π/2]` of `cos θ` times an expectation of
`⟪F' (sin θ • u + cos θ • v), G' u⟫`, and the hypothesis makes every such integrand
nonnegative.

The pointwise hypothesis `hpos` (nonnegativity of `⟪F' x, G' y⟫` for all pairs `x, y`) is
stronger than the covariance-sign hypothesis of the general positive-correlation theorem. It is
kept as stated in the source.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace LatticeProb.Pitt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Positive correlation of smooth bounded functions** under the standard Gaussian measure.
If `F` and `G` are bounded, have bounded continuous Fréchet gradients `F'` and `G'`, and
`⟪F' x, G' y⟫ ≥ 0` for all `x, y` (`hpos`), then `E[F] E[G] ≤ E[F G]`. -/
theorem integral_mul_le_integral_mul_stdGaussian {F G : E → ℝ} {F' G' : E → E}
    {CF CG CF' CG' : ℝ}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (F' x)) x) (hG : ∀ x, HasFDerivAt G (innerSL ℝ (G' x)) x)
    (hF'c : Continuous F') (hG'c : Continuous G')
    (hFb : ∀ x, |F x| ≤ CF) (hGb : ∀ x, |G x| ≤ CG)
    (hF'b : ∀ x, ‖F' x‖ ≤ CF') (hG'b : ∀ x, ‖G' x‖ ≤ CG')
    (hpos : ∀ x y, 0 ≤ ⟪F' x, G' y⟫) :
    (∫ x, F x ∂stdGaussian E) * (∫ x, G x ∂stdGaussian E) ≤
      ∫ x, F x * G x ∂stdGaussian E := by
  have toDual_eq : ∀ v : E, InnerProductSpace.toDual ℝ E v = innerSL ℝ v := fun v => by
    ext y
    simp [InnerProductSpace.toDual_apply_apply]
  have hsF : GaussConc.SmoothBdd F F' CF CF' :=
    ⟨fun x => hasGradientAt_iff_hasFDerivAt.2 (by rw [toDual_eq]; exact hF x), hF'c, hFb, hF'b⟩
  have hsG : GaussConc.SmoothBdd G G' CG CG' :=
    ⟨fun x => hasGradientAt_iff_hasFDerivAt.2 (by rw [toDual_eq]; exact hG x), hG'c, hGb, hG'b⟩
  have hcov := GaussConc.integral_mul_sub_eq_cov hsF hsG
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..(π / 2), Real.cos θ *
      ∫ p, ⟪F' (Real.sin θ • p.1 + Real.cos θ • p.2), G' p.1⟫
        ∂((stdGaussian E).prod (stdGaussian E)) := by
    refine intervalIntegral.integral_nonneg (by positivity) fun θ hθ => ?_
    exact mul_nonneg (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos, hθ.1]) hθ.2) (MeasureTheory.integral_nonneg fun p => hpos _ _)
  linarith [hcov, hnonneg]

end LatticeProb.Pitt

/-! ### Nonvacuity examples -/

namespace LatticeProb.Pitt.PittCoreExample

open MeasureTheory ProbabilityTheory Real

/-- The hypotheses of `integral_mul_le_integral_mul_stdGaussian` hold for two constant functions
on `ℝ²`: their Fréchet derivatives and gradients vanish, so `⟪0, 0⟫ = 0 ≥ 0`. -/
example (c : ℝ) :
    (∫ _, c ∂stdGaussian (EuclideanSpace ℝ (Fin 2))) *
        (∫ _, c ∂stdGaussian (EuclideanSpace ℝ (Fin 2))) ≤
      ∫ _, c * c ∂stdGaussian (EuclideanSpace ℝ (Fin 2)) :=
  integral_mul_le_integral_mul_stdGaussian (F := fun _ => c) (G := fun _ => c)
    (F' := fun _ => 0) (G' := fun _ => 0) (CF := |c|) (CG := |c|) (CF' := 0) (CG' := 0)
    (fun x => show HasFDerivAt (fun _ => c) (innerSL ℝ (0 : EuclideanSpace ℝ (Fin 2))) x by
      rw [map_zero]; exact hasFDerivAt_const c x)
    (fun x => show HasFDerivAt (fun _ => c) (innerSL ℝ (0 : EuclideanSpace ℝ (Fin 2))) x by
      rw [map_zero]; exact hasFDerivAt_const c x)
    continuous_const continuous_const (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) (fun _ _ => by simp)

end LatticeProb.Pitt.PittCoreExample
