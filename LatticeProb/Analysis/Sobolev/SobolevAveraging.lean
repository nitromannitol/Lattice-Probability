/-
# The mollification residual as an average of translation differences

For a mollifier `ρ` of mass one, the residual `f − f ⋆ ρ` is an average of the
translation
differences of `f`.  Since `convReal f ρ = convolution f ρ (mul) volume` and, by
`MeasureTheory.convolution_def`, `(f ⋆ ρ) x = ∫ t, f t * ρ (x - t)`, writing
`f x = ∫ t, f x * ρ t`
and substituting `t = x - s`, then `s = x + y`, gives the identity with the **reflected**
mollifier and the **backward** difference:

  `f x − (f ⋆ ρ) x = ∫ y, ρ (-y) • (f x − f (x + y))`.

If `ρ` is even, `ρ (-y)` may be replaced by `ρ y`.  The difference remains
`f x − f (x + y)`.

The pointwise identity needs the convolution integral to exist at `x`: where it does not, the
Bochner integral defining `convReal f ρ x` collapses to `0` and the identity fails.  For
integrable `f` and `ρ` the integral exists almost everywhere
(`MeasureTheory.Integrable.ae_convolution_exists`), and since the Sobolev norm only sees the
Fourier transform, hence only the a.e. class, the norm bound
`sobolevNormSq_sub_convReal_le` holds unconditionally.
-/
import LatticeProb.Analysis.Sobolev.SobolevToReal

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **Averaging identity**, at a point where the convolution integral exists:
`f x − (f ⋆ ρ) x = ∫ y, ρ (-y) • (f x − f (x + y))`. -/
theorem sub_convReal_eq_integral_translate {d : ℕ} {f ρ : Space d → ℝ}
    (hρ : Integrable ρ) (hmass : ∫ y, ρ y = 1) (x : Space d)
    (hx : Integrable (fun t => f t * ρ (x - t))) :
    f x - convReal f ρ x = ∫ y, ρ (-y) • (f x - f (x + y)) := by
  have h1 : Integrable (fun y => ρ (-y) * f x) := (hρ.comp_neg).mul_const _
  have h2 : Integrable (fun y => ρ (-y) * f (x + y)) := by
    have := hx.comp_add_left x
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have e1 : ∫ y, ρ (-y) * f x = f x := by
    rw [integral_mul_const, integral_neg_eq_self (fun y => ρ y) volume, hmass, one_mul]
  have e2 : ∫ y, ρ (-y) * f (x + y) = convReal f ρ x := by
    rw [convReal, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_add_left_eq_self (μ := volume) (fun t => f t * ρ (x - t)) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  calc f x - convReal f ρ x = (∫ y, ρ (-y) * f x) - ∫ y, ρ (-y) * f (x + y) := by rw [e1, e2]
    _ = ∫ y, (ρ (-y) * f x - ρ (-y) * f (x + y)) := (integral_sub h1 h2).symm
    _ = ∫ y, ρ (-y) • (f x - f (x + y)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [smul_eq_mul]; ring

/-- Almost every point of `Space d` admits the averaging identity, for integrable `f`, `ρ`. -/
theorem ae_sub_convReal_eq_integral_translate {d : ℕ} {f ρ : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) (hmass : ∫ y, ρ y = 1) :
    ∀ᵐ x : Space d,
      f x - convReal f ρ x = ∫ y, ρ (-y) • (f x - f (x + y)) := by
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hρ] with x hx
  exact sub_convReal_eq_integral_translate hρ hmass x hx

/-- The `H^s` norm only depends on the almost-everywhere class of a function. -/
theorem sobolevNormSq_congr_ae {d : ℕ} (s : ℝ) {f g : Space d → ℝ} (h : f =ᵐ[volume] g) :
    sobolevNormSq d s f = sobolevNormSq d s g := by
  have : ∀ ξ : Space d, 𝓕 (fun x => (f x : ℂ)) ξ = 𝓕 (fun x => (g x : ℂ)) ξ := by
    intro ξ
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    simp [hx]
  simp only [sobolevNormSq, this]

/-- **Averaging bound.**  The mollification residual has the same `H^s` norm as the average of
the backward translation differences against the reflected mollifier. -/
theorem sobolevNormSq_sub_convReal_le {d : ℕ} (s : ℝ) {f ρ : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) (hmass : ∫ y, ρ y = 1) :
    sobolevNormSq d s (fun x => f x - convReal f ρ x)
      ≤ sobolevNormSq d s (fun x => ∫ y, ρ (-y) • (f x - f (x + y))) :=
  (sobolevNormSq_congr_ae s (ae_sub_convReal_eq_integral_translate hf hρ hmass)).le

end LatticeProb.Sobolev
