import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Integration by parts for a time derivative which exists only on an open set.

Moved from Parking-Sharpness.
-/

open MeasureTheory MeasureTheory.Measure Filter Topology

namespace LatticeProb.Scaling.LocalTimeIntegration

/-- Integration by parts in time against a smooth compactly supported test function `ψ`, for a
continuous `u` whose time derivative `v` exists and is continuous only on an open set `O`
containing the support of `ψ`. -/
theorem integral_timeDerivative {d : ℕ}
    {u v ψ : ℝ × (Fin d → ℝ) → ℝ} {O : Set (ℝ × (Fin d → ℝ))}
    (hu : Continuous u) (hv : ContinuousOn v O) (hO : IsOpen O)
    (hderiv : ∀ p ∈ O, HasDerivAt (fun s => u (s, p.2)) (v p) p.1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ O) :
    -(∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1) =
      ∫ p : ℝ × (Fin d → ℝ), v p * ψ p := by
  letI : IsAddHaarMeasure (volume : Measure (Fin d → ℝ)) := isAddHaarMeasure_volume_pi _
  letI : IsAddHaarMeasure (volume : Measure (ℝ × (Fin d → ℝ))) := by
    change IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ)))
    infer_instance
  have hvψ : Continuous (fun p => v p * ψ p) :=
    (hv.mul hψ.continuous.continuousOn).continuous_of_tsupport_subset hO
      (tsupport_mul_subset_right.trans hsupp)
  have hvg : Integrable (fun p => v p * ψ p) :=
    hvψ.integrable_of_hasCompactSupport hψs.mul_left
  have hug : Integrable (fun p => u p * ψ p) :=
    (hu.mul hψ.continuous).integrable_of_hasCompactSupport hψs.mul_left
  have hcderiv : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ ψ p (1, 0)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × (Fin d → ℝ))).contDiff.comp
      (hψ.fderiv_right (by simp))
  have hudg : Integrable (fun p => u p * fderiv ℝ ψ p (1, 0)) :=
    (hu.mul hcderiv.continuous).integrable_of_hasCompactSupport
      (hψs.fderiv_apply (𝕜 := ℝ) (1, 0)).mul_left
  have hline : ∀ p ∈ tsupport ψ, HasLineDerivAt ℝ u (v p) p ((1, 0) : ℝ × (Fin d → ℝ)) := by
    intro p hp
    have ht := (hderiv p (hsupp hp)).scomp_of_eq (0 : ℝ)
      ((hasDerivAt_const 0 p.1).add (hasDerivAt_id 0)) (by simp)
    simpa [HasLineDerivAt, Function.comp_def, Prod.add_def, Prod.smul_def] using ht
  have hψline : ∀ p ∈ tsupport u, HasLineDerivAt ℝ ψ (fderiv ℝ ψ p (1, 0)) p
      ((1, 0) : ℝ × (Fin d → ℝ)) :=
    fun p _ => ((hψ.differentiable (by simp)) p).hasFDerivAt.hasLineDerivAt (1, 0)
  have heq := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hvg hudg hug hline hψline
  have hslice (p : ℝ × (Fin d → ℝ)) :
      deriv (fun s => ψ (s, p.2)) p.1 = fderiv ℝ ψ p (1, 0) := by
    simpa [Function.comp_def] using
      (((hψ.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv
  simp_rw [hslice]
  simpa using congrArg Neg.neg heq

end LatticeProb.Scaling.LocalTimeIntegration
