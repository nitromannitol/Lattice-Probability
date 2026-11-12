import Mathlib
import LatticeProb.Gauss.CameronMartinLimitShift
import LatticeProb.Gauss.UncorrelatedIndependence

/-!
# Exponential tilt of a Gaussian process by a scaled coordinate

Let `Y = (Y t)_{t ∈ T}` be a centred Gaussian process, `q ∈ T` and `γ ∈ ℝ`. Weighting `P` by the exponential
martingale `exp (γ Y q - γ² Var(Y q) / 2)` shifts the law of the whole family by `γ Cov(·, Y q)` (the Cameron-Martin
or Girsanov theorem; Berestycki-Powell, *Gaussian free field and Liouville quantum gravity*, Lemma 1.31): for every
measurable `Φ : (T → ℝ) → ℝ≥0∞` on the product σ-algebra,
`E[exp(γ Y q - γ² Var(Y q)/2) Φ(Y)] = E[Φ(Y + γ Cov(Y, Y q))]`.

* `lintegral_exp_mul_tilt`: the identity above, deduced from `map_shift_withDensity_eq_map` applied to the process
  indexed by `Option T` with the extra coordinate `-γ Y q`.
-/

noncomputable section

namespace LatticeProb.Gauss

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Exponential tilt by a scaled coordinate.** For a centred Gaussian process `Y`, a coordinate `q` and `γ ∈ ℝ`,
`E[exp(γ Y q - γ² Var(Y q)/2) Φ(Y)] = E[Φ(Y + γ Cov(Y, Y q))]` for every measurable `Φ ≥ 0` on paths. -/
theorem lintegral_exp_mul_tilt {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) (γ : ℝ)
    {Φ : (T → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (γ * Y q x - γ ^ 2 * Var[Y q; P] / 2)) * Φ (fun t => Y t x) ∂P
      = ∫⁻ x, Φ (fun t => Y t x + γ * cov[Y t, Y q; P]) ∂P := by
  classical
  let Y' : Option T → Ω → ℝ := fun o => Option.elim o (fun x => -γ * Y q x) Y
  have hnone : Y' none = fun x => -γ * Y q x := rfl
  have hsome : ∀ t, Y' (some t) = Y t := fun _ => rfl
  have hY'G : IsGaussianProcess Y' P :=
    LatticeProb.GaussIndep.isGaussianProcess_of_mem_span hY fun o => by
      cases o with
      | none =>
        have h : Y' none = (-γ) • Y q := by rw [hnone]; rfl
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
      | some t => exact Submodule.subset_span ⟨t, rfl⟩
  have hY'm : ∀ o, Measurable (Y' o) := fun o => by
    cases o with
    | none => rw [hnone]; exact (hYm q).const_mul _
    | some t => rw [hsome]; exact hYm t
  have hY'cen : ∀ o, P[Y' o] = 0 := fun o => by
    cases o with
    | none => rw [hnone, integral_const_mul, hcen q, mul_zero]
    | some t => rw [hsome]; exact hcen t
  have key := map_shift_withDensity_eq_map hY'G hY'm hY'cen none
  have hvar : Var[Y' none; P] = γ ^ 2 * Var[Y q; P] := by
    rw [hnone, variance_const_mul, neg_sq]
  have hcov : ∀ t, cov[Y' (some t), Y' none; P] = -γ * cov[Y t, Y q; P] := fun t => by
    rw [hsome, hnone, covariance_const_mul_right]
  set D : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-Y' none x - Var[Y' none; P] / 2)) with hDdef
  have hD : Measurable D :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((hY'm none).neg).sub_const _))
  let Ψ : (Option T → ℝ) → ℝ≥0∞ := fun y => Φ (fun t => y (some t) + γ * cov[Y t, Y q; P])
  have hΨ : Measurable Ψ :=
    hΦ.comp (measurable_pi_iff.2 fun t => (measurable_pi_apply (some t)).add_const _)
  have hF'm : Measurable (fun x o => Y' o x + cov[Y' o, Y' none; P]) :=
    measurable_pi_iff.2 fun o => (hY'm o).add_const _
  have hFm : Measurable (fun x o => Y' o x) := measurable_pi_iff.2 hY'm
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (γ * Y q x - γ ^ 2 * Var[Y q; P] / 2)) * Φ (fun t => Y t x) ∂P
      = ∫⁻ x, (D * fun x => Ψ (fun o => Y' o x + cov[Y' o, Y' none; P])) x ∂P := by
        refine lintegral_congr fun x => ?_
        have h1 : (fun t => (Y' (some t) x + cov[Y' (some t), Y' none; P]) + γ * cov[Y t, Y q; P])
            = fun t => Y t x := by
          funext t
          rw [hcov t, hsome]
          ring
        have h2 : -Y' none x - Var[Y' none; P] / 2 = γ * Y q x - γ ^ 2 * Var[Y q; P] / 2 := by
          rw [hvar]
          simp only [hnone]
          ring
        show _ = ENNReal.ofReal (Real.exp (-Y' none x - Var[Y' none; P] / 2)) *
          Φ (fun t => (Y' (some t) x + cov[Y' (some t), Y' none; P]) + γ * cov[Y t, Y q; P])
        rw [h1, h2]
    _ = ∫⁻ x, Ψ (fun o => Y' o x + cov[Y' o, Y' none; P]) ∂(P.withDensity D) :=
        (lintegral_withDensity_eq_lintegral_mul _ hD (hΨ.comp hF'm)).symm
    _ = ∫⁻ y, Ψ y ∂((P.withDensity D).map fun x o => Y' o x + cov[Y' o, Y' none; P]) :=
        (lintegral_map hΨ hF'm).symm
    _ = ∫⁻ y, Ψ y ∂(P.map fun x o => Y' o x) := by rw [key]
    _ = ∫⁻ x, Φ (fun t => Y t x + γ * cov[Y t, Y q; P]) ∂P := by
        exact lintegral_map hΨ hFm

end LatticeProb.Gauss
