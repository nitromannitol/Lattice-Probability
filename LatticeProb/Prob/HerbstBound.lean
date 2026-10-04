/-
The integration step of the Herbst argument.

`LatticeProb.Prob.HerbstFromLSI` proves that the Gaussian log-Sobolev inequality
gives the entropy bound `Ent(h_λ) ≤(λ L)² / 2` for the tilted density
`h_λ = exp(λ (f - ∫f)) / M(λ)` of an `L`-Lipschitz functional `f`, where
`M(λ) = ∫ exp(λ (f - ∫f))` is the moment generating function of `f - ∫f`.
Writing `P = log M`, that entropy bound is `λ P'(λ) - P(λ) ≤ (λ L)² / 2`, the
differential inequality for `M`.

This module finishes the argument.  It differentiates `M` under the integral
sign, turns the entropy bound into `(P(λ)/λ)' ≤ L²/2`, uses the convexity limit
`P(λ)/λ → P'(0) = 0`, and concludes `M(λ) ≤ exp(λ² L² / 2)`, which is
`LatticeProb.GaussianHerbstBound n`.  Together with `HerbstFromLSI` this reduces
the Gaussian Herbst exponential moment bound to the Gaussian log-Sobolev
inequality.

The argument is the classical one of Herbst (1975), as presented in Ledoux,
*The Concentration of Measure Phenomenon*, Section 5.1.
-/
import LatticeProb.Prob.HerbstFromLSI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace LatticeProb

/-- **Differentiation of the moment generating function.**  For an `L`-Lipschitz
`f`, the moment generating function `t ↦ ∫ exp (t (f - ∫f))` of the centred
functional is differentiable, with derivative the corresponding first moment:
`(d/dt) ∫ exp (t (f - ∫f)) = ∫ (f - ∫f) exp (t (f - ∫f))`. -/
theorem hasDerivAt_mgf_centred (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (lam : ℝ) :
    HasDerivAt (fun t => ∫ x, Real.exp (t * (f x - ∫ y, f y
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (∫ x, (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))
        * Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) lam := by
  set g : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y
    ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) with hg
  have hgL : LipschitzWith ⟨L, hL.le⟩ g := lipschitzWith_sub_integral n f L hL.le hf
  have hgcont : Continuous g := hgL.continuous
  have hc0 : (0 : ℝ) ≤ |lam| + 1 := by positivity
  -- The dominating function `|g| exp ((|lam|+1) |g|)` is integrable.
  have hbound_int : Integrable (fun x => |g x| * Real.exp ((|lam| + 1) * |g x|))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have hpos : Integrable (fun x => |g x| * Real.exp ((|lam| + 1) * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      refine (integrable_mul_exp_sub_integral n f L (|lam| + 1) hL hf).norm.congr ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hneg : Integrable (fun x => |g x| * Real.exp (-(|lam| + 1) * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      refine (integrable_mul_exp_sub_integral n f L (-(|lam| + 1)) hL hf).norm.congr ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine (hpos.add hneg).mono' ?_ ?_
    · exact (hgcont.abs.mul (Real.continuous_exp.comp
        (continuous_const.mul hgcont.abs))).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      simp only [Pi.add_apply]
      rcases le_total 0 (g x) with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_add_of_nonneg_right (mul_nonneg hx (Real.exp_pos _).le)
      · rw [abs_of_nonpos hx]
        rw [show (|lam| + 1) * -g x = -(|lam| + 1) * g x by ring]
        exact le_add_of_nonneg_left (mul_nonneg (neg_nonneg.mpr hx) (Real.exp_pos _).le)
  -- Measurability and integrability of the family.
  have hF_meas : ∀ᶠ t in 𝓝 lam,
      AEStronglyMeasurable (fun x => Real.exp (t * g x))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    Filter.Eventually.of_forall fun t =>
      (Real.continuous_exp.comp (continuous_const.mul hgcont)).aestronglyMeasurable
  have hF_int : Integrable (fun x => Real.exp (lam * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    integrable_exp_sub_integral n f L lam hL hf
  have hF'_meas : AEStronglyMeasurable (fun x => g x * Real.exp (lam * g x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    (hgcont.mul (Real.continuous_exp.comp (continuous_const.mul hgcont))).aestronglyMeasurable
  have h_diff : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      ∀ t ∈ Set.Ioo (lam - 1) (lam + 1),
        HasDerivAt (fun s => Real.exp (s * g x)) (g x * Real.exp (t * g x)) t := by
    filter_upwards with x
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s * g x) (1 * g x) t :=
      (hasDerivAt_id t).mul_const (g x)
    have h2 := h1.exp
    simpa only [one_mul, mul_comm] using h2
  have h_bound : ∀ᵐ x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1),
      ∀ t ∈ Set.Ioo (lam - 1) (lam + 1),
        ‖g x * Real.exp (t * g x)‖ ≤ |g x| * Real.exp ((|lam| + 1) * |g x|) := by
    filter_upwards with x
    intro t ht
    have htabs : |t| ≤ |lam| + 1 := by
      rw [abs_le]
      constructor
      · have h1 : -(|lam| + 1) ≤ lam - 1 := by
          have := neg_abs_le lam; linarith
        linarith [ht.1]
      · have h2 : lam + 1 ≤ |lam| + 1 := by linarith [le_abs_self lam]
        linarith [ht.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : t * g x ≤ (|lam| + 1) * |g x| := by
      calc t * g x ≤ |t * g x| := le_abs_self _
        _ = |t| * |g x| := by rw [abs_mul]
        _ ≤ (|lam| + 1) * |g x| := by
            exact mul_le_mul_of_nonneg_right htabs (abs_nonneg _)
    calc |g x| * Real.exp (t * g x) ≤ |g x| * Real.exp ((|lam| + 1) * |g x|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (abs_nonneg _)
      _ = |g x| * Real.exp ((|lam| + 1) * |g x|) := rfl
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (lam - 1) (lam + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) hF_meas hF_int hF'_meas h_bound
    hbound_int h_diff).2

end LatticeProb
