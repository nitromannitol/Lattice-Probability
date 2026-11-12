import LatticeProb.LQG.InternalMetricSquareTail
import LatticeProb.LQG.LQGMetricInternalScaling
import LatticeProb.LQG.WeylChainBound

/-!
# Internal diameter of a small square for a Weyl-scaled γ-LQG metric

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF and `S = [Re c, Re c + t] × [Im c, Im c + t]` a closed square of side
`t > 0` with lower-left corner `c`. By the coordinate change for scaling and translation, the internal metric of `D_h`
on `S` is `e^{ξ (h_t(c) + Q log t)}` times the internal metric of `D_{h'}` on the closed unit square, where
`h' = h(t · + c) - h_t(c)` is again a whole-plane GFF. Combined with the Weyl comparison for a weight with `ξ f ≤ B` on
`S`, this bounds the internal diameter of `S` for `E = e^{ξ f} · D_h` by `e^B e^{ξ (h_t(c) + Q log t)}` times the
internal diameter of the unit square for `D_{h'}`. This is the one-square estimate used when chaining over squares of
all scales towards a point.

## Main statements

* `LatticeProb.LQG.affine_image_unitSquare`: `z ↦ t z + c` maps the closed unit square onto `S`.
* `LatticeProb.LQG.IsLQGMetric.ae_internalMetric_square_le_of_weylScaling`: the one-square estimate.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- The affine map `z ↦ t z + c` with `t > 0` maps the closed unit square onto the closed square
`[Re c, Re c + t] × [Im c, Im c + t]`. -/
theorem affine_image_unitSquare {t : ℝ} (ht : 0 < t) (c : ℂ) :
    (fun z : ℂ => (t : ℂ) * z + c) '' (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) =
      Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · intro hw
    rw [Complex.mem_reProdIm] at hw
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
    refine ⟨(w - c) / t, ?_, ?_⟩
    · rw [Complex.mem_reProdIm, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im]
      exact ⟨⟨div_nonneg (by linarith) ht.le, (div_le_one ht).2 (by linarith)⟩,
        ⟨div_nonneg (by linarith) ht.le, (div_le_one ht).2 (by linarith)⟩⟩
    · have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
      show (t : ℂ) * ((w - c) / t) + c = w
      rw [mul_div_assoc', mul_div_cancel_left₀ _ ht', sub_add_cancel]

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **One-square estimate for a Weyl-scaled γ-LQG metric.** Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF, `t > 0`,
`c ∈ ℂ` and `S = [Re c, Re c + t] × [Im c, Im c + t]`. Let `E` be a random function which is almost surely the Weyl
scaling `e^{ξ f} · D_h`, with `ξ f ≤ B` on `S` almost surely. Then almost surely, for every `A ∈ [0, ∞]`: if the internal
diameter of the closed unit square for `D_{h'}`, `h' = h(t · + c) - h_t(c)` (`recentredPairing`), is at most `A`, then
`E(u, v; S) ≤ e^B e^{ξ (h_t(c) + Q log t)} A` for all `u, v ∈ S`. -/
theorem IsLQGMetric.ae_internalMetric_square_le_of_weylScaling (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {t : ℝ} (ht : 0 < t) (c : ℂ) {E : Ω → ℂ → ℂ → ℝ} {f : Ω → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ (f ω) x y) {B : ℝ}
    (hf : ∀ᵐ ω ∂P, ∀ z ∈ Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t), ξ * f ω z ≤ B) :
    ∀ᵐ ω ∂P, ∀ A : ℝ≥0∞,
      (∀ u ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        internalMetric (𝔇 (recentredPairing hC hcirc t c ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u v ≤ A) →
      ∀ u ∈ Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t), ∀ v ∈ Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t),
        internalMetric (E ω) (Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t)) u v ≤
          ENNReal.ofReal (Real.exp B) *
            (ENNReal.ofReal (Real.exp (ξ * (hcirc ω t c + lqgQ γ * Real.log t))) * A) := by
  have himg := affine_image_unitSquare ht c
  filter_upwards [h𝔇.ae_internalMetric_scaling hG ht c, h𝔇.ae_isEuclideanLengthMetric_self hG, hE, hf]
    with ω hsc hD hEω hB A hA u hu v hv
  rw [← himg] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  calc internalMetric (E ω) (Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t)) ((t : ℂ) * u' + c) ((t : ℂ) * v' + c)
      ≤ ENNReal.ofReal (Real.exp B) * internalMetric (𝔇 (hC ω))
          (Icc c.re (c.re + t) ×ℂ Icc c.im (c.im + t)) ((t : ℂ) * u' + c) ((t : ℂ) * v' + c) :=
        internalMetric_le_of_weylScaling hD hEω hB _ _
    _ = ENNReal.ofReal (Real.exp B) * (ENNReal.ofReal (Real.exp (ξ * (hcirc ω t c + lqgQ γ * Real.log t))) *
          internalMetric (𝔇 (recentredPairing hC hcirc t c ω)) (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) u' v') := by
        rw [← himg, hsc]
    _ ≤ _ := by gcongr; exact hA u' hu' v' hv'

end LatticeProb.LQG
