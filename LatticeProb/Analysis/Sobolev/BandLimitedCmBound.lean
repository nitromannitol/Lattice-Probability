/-
# The band-limited `Cᵐ` bound in `L²` and `H^s`

This module assembles the band-limited Bernstein bound of
`BandLimitedBernstein.lean` — stated in the `L¹`-on-the-band form
`‖D^k (𝓕⁻ ψ) x‖ ≤ (2π·2Λ)^k ∫_{‖ξ‖≤2Λ} ‖ψ ξ‖ dξ` — into the two forms the
low-frequency net consumes:

* `exists_iteratedFDeriv_bandTrunc_le_L2`: the `L²` form, bounding the `k`-th
  derivative of the truncation `P_Λ F` by a constant times `‖F‖_{L²}`;
* `exists_iteratedFDeriv_bandProj_le` and `BandLimitedCmBound`: the `H^s` form
  for `s ≥ 0` and for the real-valued projection `bandProj` of a test function,
  i.e. the uniform `C^m` bound of the low-frequency family on the `H^s` unit ball.

The passage from `L¹` to `L²` is Cauchy–Schwarz on the band
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`, on the
restricted measure `volume.restrict (ball 0 (2Λ))`), and the passage from `L²` to
`H^s` is the monotonicity of the Sobolev weight in `s ≥ 0`
(`sobolevNormSq_mono`) together with `‖χ_Λ · 𝓕 φ‖ ≤ ‖𝓕 φ‖` (`0 ≤ χ_Λ ≤ 1`).
Neither step needs Plancherel: the `H^s` bound is obtained directly against the
`H^s` integral.
-/
import LatticeProb.Analysis.Sobolev.BandLimitedBernstein
import LatticeProb.Analysis.Sobolev.BandTruncReal
import LatticeProb.Analysis.Sobolev.Weight

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace

namespace LatticeProb.Sobolev

/-- **Cauchy–Schwarz on a ball.**  The `L¹` integral of `‖f‖` over a ball is at
most the square root of the volume of the ball times the `L²` integral of
`‖f‖²`. -/
private theorem integral_norm_le_sqrt_volume_mul_sqrt_sq {d : ℕ} {f : Space d → ℂ}
    (hf : MemLp f 2 volume) (Λ : ℝ) :
    ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖f ξ‖
      ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
        * Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space d) (2 * Λ))) := by
    rw [isFiniteMeasure_iff]
    simp only [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hf1 : MemLp (fun ξ : Space d => ‖f ξ‖) (ENNReal.ofReal 2)
      (volume.restrict (Metric.ball (0 : Space d) (2 * Λ))) := by
    simpa using hf.norm.mono_measure
      (Measure.restrict_le_self (s := Metric.ball (0 : Space d) (2 * Λ)))
  have hg1 : MemLp (fun _ : Space d => (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Metric.ball (0 : Space d) (2 * Λ))) := by
    simpa using (memLp_const (μ := volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      (p := (2 : ℝ≥0∞)) (1 : ℝ))
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (μ := volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hf1 hg1
  have hleft : ∫ a, ‖f a‖ * (1 : ℝ) ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = ∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ := by
    simp only [mul_one]
  have hA : ∫ a, ‖f a‖ ^ (2 : ℝ) ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = ∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => Real.rpow_two _)
  have hB : ∫ a, (1 : ℝ) ^ (2 : ℝ) ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal := by
    simp only [Real.one_rpow, integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
      Measure.real]
  rw [hleft, hA, hB] at hholder
  have hmono : (∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2)
      ≤ ∫ a, ‖f a‖ ^ 2 :=
    setIntegral_le_integral
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf)
      (Filter.Eventually.of_forall fun a => sq_nonneg _)
  have hsqrt : (∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫ a, ‖f a‖ ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hmono (by norm_num)
  have hvol : (0 : ℝ) ≤ (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal :=
    ENNReal.toReal_nonneg
  refine hholder.trans ?_
  calc (∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2) ^ (1 / 2 : ℝ)
        * (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal ^ (1 / 2 : ℝ)
      ≤ (∫ a, ‖f a‖ ^ 2) ^ (1 / 2 : ℝ)
        * (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hvol _)
    _ = Real.sqrt (∫ a, ‖f a‖ ^ 2)
        * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
        * Real.sqrt (∫ a, ‖f a‖ ^ 2) := mul_comm _ _

theorem exists_iteratedFDeriv_bandTrunc_le_L2 {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : 𝓢(Space d, ℂ)) (x : Space d),
      ‖iteratedFDeriv ℝ k (fun y => bandTrunc d Λ hΛ.ne' F y) x‖
        ≤ C * Real.sqrt (∫ ξ, ‖𝓕 F ξ‖ ^ 2) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_iteratedFDeriv_bandTrunc_le (d := d) Λ hΛ k
  refine ⟨C₀ * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal) + 1,
    by positivity, fun F x => ?_⟩
  have hcs := integral_norm_le_sqrt_volume_mul_sqrt_sq ((𝓕 F).memLp 2 volume) Λ
  have hsq : (0 : ℝ) ≤ Real.sqrt (∫ ξ, ‖𝓕 F ξ‖ ^ 2) :=
    Real.sqrt_nonneg _
  have hvol : (0 : ℝ) ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal) :=
    Real.sqrt_nonneg _
  calc ‖iteratedFDeriv ℝ k (fun y => bandTrunc d Λ hΛ.ne' F y) x‖
      ≤ C₀ * ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖𝓕 F ξ‖ := hbound F x
    _ ≤ C₀ * (Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
          * Real.sqrt (∫ ξ, ‖𝓕 F ξ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hC₀
    _ ≤ (C₀ * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal) + 1)
          * Real.sqrt (∫ ξ, ‖𝓕 F ξ‖ ^ 2) := by
        nlinarith [hC₀, hsq, hvol]

/-- The `H^0` norm is the squared `L²` norm of the Fourier transform: this is the
`L²` Bernstein form rewritten against `sobolevNormSq d 0`. -/
private theorem toReal_sobolevNormSq_zero {d : ℕ} (φ : Space d → ℝ)
    (hint : Integrable (fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) volume) :
    (sobolevNormSq d 0 φ).toReal = ∫ ξ, ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := by
  have hnn : 0 ≤ᵐ[volume] fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 :=
    Filter.Eventually.of_forall fun ξ => sq_nonneg _
  have h : sobolevNormSq d 0 φ
      = ENNReal.ofReal (∫ ξ, ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    rw [sobolevNormSq]
    simp only [Real.rpow_zero, one_mul]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  rw [h, ENNReal.toReal_ofReal (integral_nonneg fun ξ => sq_nonneg _)]

/-- **The band-limited `C^m` bound in `H^s`.**  For `s ≥ 0`, the `k`-th derivative of
the truncation `P_Λ` of a real test function is bounded on the `H^s` unit ball by a
constant depending only on `Λ`, `d` and `k`. -/
theorem exists_iteratedFDeriv_bandTrunc_le_Hs {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ}
    (hs : 0 ≤ s) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ) (x : Space d),
      sobolevNormSq d s φ ≤ 1 →
        ‖iteratedFDeriv ℝ k
            (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
          ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_iteratedFDeriv_bandTrunc_le_L2 (d := d) Λ hΛ k
  refine ⟨C, hC, fun φ hcont hcs x hnorm => ?_⟩
  have hint : Integrable (fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) volume := by
    have hmem : MemLp (fun ξ : Space d => 𝓕 (realToComplexSchwartz d φ hcont hcs) ξ) 2 volume :=
      (𝓕 (realToComplexSchwartz d φ hcont hcs)).memLp 2 volume
    have h2 : Integrable (fun ξ : Space d => ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2)
        volume :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    refine h2.congr ?_
    filter_upwards with ξ
    rw [fourier_realToComplexSchwartz d φ hcont hcs]
  have hmono : sobolevNormSq d 0 φ ≤ sobolevNormSq d s φ := sobolevNormSq_mono hs φ
  have hle1 : (sobolevNormSq d 0 φ).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hmono.trans hnorm)
    simpa using this
  have hsqrt : Real.sqrt (∫ ξ, ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) ≤ 1 := by
    rw [← toReal_sobolevNormSq_zero φ hint, Real.sqrt_le_one]
    exact hle1
  calc ‖iteratedFDeriv ℝ k
          (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
      ≤ C * Real.sqrt
          (∫ ξ, ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        have h := hbound (realToComplexSchwartz d φ hcont hcs) x
        simp_rw [fourier_realToComplexSchwartz d φ hcont hcs] at h
        exact h
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hsqrt hC.le
    _ = C := mul_one _

/-- **The band-limited `C^m` bound, packaged.**  For every cutoff `Λ > 0`, every
`s ≥ 0` and every order `k`, the `k`-th derivative of the truncation `P_Λ` of a
test function is uniformly bounded over the `H^s` unit ball.  This is the input
that makes the low-frequency family totally bounded (`Arzelà–Ascoli`), and it is
what `rkLowFreqNet` consumes. -/
def BandLimitedCmBound (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (s : ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (x : Space d),
      sobolevNormSq d s φ ≤ 1 →
        ‖iteratedFDeriv ℝ k
            (fun y => bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs) y) x‖
          ≤ C

/-- `BandLimitedCmBound` holds for every cutoff and every `s ≥ 0`. -/
theorem bandLimitedCmBound_holds {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ} (hs : 0 ≤ s) :
    BandLimitedCmBound d Λ hΛ.ne' s :=
  fun k => exists_iteratedFDeriv_bandTrunc_le_Hs Λ hΛ hs k

end LatticeProb.Sobolev
