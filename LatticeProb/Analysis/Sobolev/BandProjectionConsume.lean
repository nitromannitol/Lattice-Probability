/-
# The sharp band projection and the truncation error it leaves

`rkLowFreqNet` (`RellichLowFreqNet.lean`) consumes a bound on how far a test
function is from a band-limited function when its high-frequency content is
small.  The natural such band-limited function is the smooth projection
`bandProj d Λ φ`, whose Fourier transform is `bandCut d Λ · 𝓕 φ`
(`fourier_bandProj`, `FejerLimit.lean`); `bandCut d Λ` is `1` on `‖ξ‖ ≤ Λ` and
`0` on `‖ξ‖ ≥ 2Λ`.

This module records the two facts the residual needs.

* `bandProj_sobolevNormSqHigh_eq_zero_of_le` — `P_Λ φ := bandProj d Λ φ` is
  band-limited: its high-frequency `H^s` part vanishes at every radius
  `Λ' ≥ 2Λ`.  This is `sobolevNormSqHigh_bandProj_eq_zero` transported along
  `isBandLimited_mono`; nothing is reproved.
* `sobolevNormSq_sub_bandProj_le` — the **truncation error**: the `H^s` distance
  from `φ` to `P_Λ φ` is at most the high-frequency `H^s` content of `φ` above
  `Λ`,
  `‖φ - P_Λ φ‖²_{H^s} ≤ ∫_{‖ξ‖ > Λ} (1 + (2π‖ξ‖)²)^s ‖𝓕φ‖²`.
  Indeed `𝓕(φ - P_Λ φ) = (1 - bandCut) · 𝓕φ`, which is supported on `‖ξ‖ > Λ`
  and bounded by `‖𝓕φ‖` because `0 ≤ bandCut ≤ 1`.
* `sobolevNormSq_sub_bandProj_le_of_high` — the `δ/2` form the residual consumes.

The cutoff radius is `2Λ` for the band property and `Λ` for the error bound;
this is the same `rOut = 2` convention recorded in `lib-bandtrunc-real.md`, and
it is harmless: the band vanishes on the closed complement `‖ξ‖ ≥ 2Λ`, so no
boundary/null-set argument is needed.
-/
import LatticeProb.Analysis.Sobolev.FejerLimit
import LatticeProb.Analysis.Sobolev.Truncation
import LatticeProb.Analysis.Sobolev.Additivity

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- Subtraction of the Fourier integral for integrable functions. -/
private theorem fourier_sub_of_integrable {d : ℕ} {f g : Space d → ℝ}
    (hf : Integrable (fun x => (f x : ℂ))) (hg : Integrable (fun x => (g x : ℂ)))
    (ξ : Space d) :
    𝓕 (fun x => ((f x - g x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (f x : ℂ)) ξ - 𝓕 (fun x => (g x : ℂ)) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Circle.smul_def, Complex.ofReal_sub]
    ring
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hf
  · exact (Real.fourierIntegral_convergent_iff ξ).mpr hg

/-- The complexification of the real projection is the complex Schwartz
truncation, so `bandProj d Λ φ` inherits integrability from `bandTrunc`. -/
private theorem coe_bandProj (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    (fun x => (bandProj d Λ hΛ φ hcont hcs x : ℂ))
      = ⇑(bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) := by
  funext x
  apply Complex.ext
  · change (((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re : ℂ).re
      = ((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re
    exact Complex.ofReal_re _
  · change (((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re : ℂ).im
      = ((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).im
    rw [Complex.ofReal_im]
    exact (bandTrunc_im_eq_zero d Λ hΛ _ (fun y => by simp) x).symm

/-- **The sharp band projection is band-limited.**  For `Λ' ≥ 2Λ` the high
frequency part of `bandProj d Λ φ` vanishes in every order `s`.  This reuses
`sobolevNormSqHigh_bandProj_eq_zero` (`FejerLimit.lean`) through the
monotonicity `isBandLimited_mono`. -/
theorem bandProj_sobolevNormSqHigh_eq_zero_of_le {d : ℕ} {Λ Λ' : ℝ} (hΛ : 0 < Λ)
    (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (s : ℝ) (hΛ' : 2 * Λ ≤ Λ') :
    sobolevNormSqHigh d s Λ' (bandProj d Λ hΛ.ne' φ hcont hcs) = 0 :=
  sobolevNormSqHigh_eq_zero_of_isBandLimited (s := s)
    (isBandLimited_mono hΛ' (isBandLimited_bandProj d Λ hΛ φ hcont hcs))

/-- **The truncation error.**  The `H^s` distance from a test function `φ` to its
sharp band projection `bandProj d Λ φ` is at most the high-frequency `H^s`
content of `φ` above `Λ`.  This is the estimate the low-frequency net
`rkLowFreqNet` consumes. -/
theorem sobolevNormSq_sub_bandProj_le (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (s : ℝ) :
    sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
      ≤ sobolevNormSqHigh d s Λ φ := by
  have hφint : Integrable (fun x => (φ x : ℂ)) :=
    (Complex.continuous_ofReal.comp hcont.continuous).integrable_of_hasCompactSupport
      (hcs.comp_left (g := Complex.ofReal) (by simp))
  have hPint : Integrable (fun x => (bandProj d Λ hΛ.ne' φ hcont hcs x : ℂ)) := by
    rw [coe_bandProj d Λ hΛ.ne' φ hcont hcs]
    exact (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs)).integrable
  unfold sobolevNormSq sobolevNormSqHigh
  rw [← MeasureTheory.lintegral_indicator
    (measurableSet_lt measurable_const continuous_norm.measurable)]
  apply lintegral_mono
  intro ξ
  beta_reduce
  rw [fourier_sub_of_integrable hφint hPint ξ,
    fourier_bandProj d Λ hΛ.ne' φ hcont hcs ξ,
    show 𝓕 (fun x => (φ x : ℂ)) ξ - (bandCut d Λ ξ : ℂ) * 𝓕 (fun x => (φ x : ℂ)) ξ
        = (1 - (bandCut d Λ ξ : ℂ)) * 𝓕 (fun x => (φ x : ℂ)) ξ by ring]
  by_cases hξ : Λ < ‖ξ‖
  · rw [Set.indicator_of_mem (s := {a : Space d | Λ < ‖a‖})
      (show ξ ∈ {a : Space d | Λ < ‖a‖} from hξ)]
    apply ENNReal.ofReal_le_ofReal
    have hw : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := Real.rpow_nonneg (by positivity) s
    have hle : ‖(1 - (bandCut d Λ ξ : ℂ)) * 𝓕 (fun x => (φ x : ℂ)) ξ‖
        ≤ ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ := by
      rw [norm_mul]
      have h1 : ‖(1 : ℂ) - (bandCut d Λ ξ : ℂ)‖ ≤ 1 := by
        have hcast : (1 : ℂ) - (bandCut d Λ ξ : ℂ) = ((1 - bandCut d Λ ξ : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hcast]
        have hnorm : ‖((1 - bandCut d Λ ξ : ℝ) : ℂ)‖ = |1 - bandCut d Λ ξ| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
        rw [hnorm, abs_le]
        refine ⟨by linarith [bandCut_le_one d Λ ξ], by linarith [bandCut_nonneg d Λ ξ]⟩
      calc ‖(1 : ℂ) - (bandCut d Λ ξ : ℂ)‖ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖
          ≤ 1 * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ := one_mul _
    have hsq : ‖(1 - (bandCut d Λ ξ : ℂ)) * 𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2
        ≤ ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := by
      nlinarith [hle, norm_nonneg ((1 - (bandCut d Λ ξ : ℂ)) * 𝓕 (fun x => (φ x : ℂ)) ξ),
        norm_nonneg (𝓕 (fun x => (φ x : ℂ)) ξ)]
    exact mul_le_mul_of_nonneg_left hsq hw
  · rw [Set.indicator_of_notMem (s := {a : Space d | Λ < ‖a‖})
      (show ξ ∉ {a : Space d | Λ < ‖a‖} from hξ)]
    have hbc : bandCut d Λ ξ = 1 := bandCut_eq_one d Λ hΛ (not_lt.mp hξ)
    rw [hbc]
    norm_num

/-- **The truncation error in the form `rkLowFreqNet` consumes.**  A test
function whose high-frequency `H^s` content above `Λ` is at most `δ/2` is within
`δ/2` of its sharp band projection in `H^s`. -/
theorem sobolevNormSq_sub_bandProj_le_of_high (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ)
    (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (s δ : ℝ) (hhigh : sobolevNormSqHigh d s Λ φ ≤ ENNReal.ofReal (δ / 2)) :
    sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
      ≤ ENNReal.ofReal (δ / 2) :=
  (sobolevNormSq_sub_bandProj_le d Λ hΛ φ hcont hcs s).trans hhigh

/-- The same bound with the accuracy `δ` rather than `δ/2`, the literal form of
the ball radius in `rkLowFreqNet`. -/
theorem sobolevNormSq_sub_bandProj_le_of_high_delta (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ)
    (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (s δ : ℝ) (hδ : 0 ≤ δ)
    (hhigh : sobolevNormSqHigh d s Λ φ ≤ ENNReal.ofReal (δ / 2)) :
    sobolevNormSq d s (fun x => φ x - bandProj d Λ hΛ.ne' φ hcont hcs x)
      ≤ ENNReal.ofReal δ := by
  refine (sobolevNormSq_sub_bandProj_le_of_high d Λ hΛ φ hcont hcs s δ hhigh).trans ?_
  exact ENNReal.ofReal_le_ofReal (by linarith)

end LatticeProb.Sobolev
