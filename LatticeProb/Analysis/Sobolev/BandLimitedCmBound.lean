/-
# The band-limited `Cᵐ` bound in `L²` and `H^s`

This module assembles the band-limited Bernstein bound of
`BandLimitedBernstein.lean` — stated in the `L¹`-on-the-band form
`‖D^k (𝓕⁻ ψ) x‖ ≤ (2π·2Λ)^k ∫_{‖ξ‖≤2Λ} ‖ψ ξ‖ dξ`
— into the two forms that the low-frequency net consumes:

* `exists_iteratedFDeriv_bandTrunc_le_L2`: the `L²` form, bounding the `k`-th
  derivative of the truncation `P_Λ F` by a constant times `‖F‖_{L²}`;
* `exists_iteratedFDeriv_bandProj_le` and `BandLimitedCmBound`: the `H^s` form
  for `s ≥ 0` and for the real-valued projection `bandProj` of a test function,
  i.e. the uniform `C^m` bound of the low-frequency family on the `H^s` unit ball.

The passage from `L¹` to `L²` is Cauchy–Schwarz on the band
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`, on the
restricted measure `volume.restrict (ball 0 (2Λ))`), and the passage from `L²` to
`H^s` is the monotonicity of the Sobolev weight in `s ≥ 0`
(`sobolevNormSq_mono`) together with `‖χ_Λ · 𝓕 φ‖ ≤ ‖𝓕 φ‖`
(`0 ≤ χ_Λ ≤ 1`).
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
  have hleft : ∫ a, ‖f a‖ * (1 : ℝ)
        ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
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
  have hint : Integrable
      (fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) volume := by
    have hmem : MemLp
        (fun ξ : Space d => 𝓕 (realToComplexSchwartz d φ hcont hcs) ξ) 2 volume :=
      (𝓕 (realToComplexSchwartz d φ hcont hcs)).memLp 2 volume
    have h2 : Integrable
        (fun ξ : Space d => ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2) volume :=
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

/-! ### The negative-order case

The `H^s` bound above used `sobolevNormSq d 0 φ ≤ sobolevNormSq d s φ`
(`sobolevNormSq_mono`), which holds only for `s ≥ 0`: for `s < 0` the `H^s` norm
is *weaker* than `L²`, so it does not dominate it.  The pointwise route does
work in every order, though.  On the band `‖ξ‖ ≤ 2Λ` the Sobolev weight
`w(ξ) = 1 + (2π‖ξ‖)²` lies in `[1, M]` with `M = 1 + (2π·2Λ)²`, so

`1 ≤ M^{|s|} · w(ξ)^s`

(`M^{|s|} = M^s` with both factors at least one for `s ≥ 0`; and
`M^{|s|} w^s = (M/w)^{-s} ≥ 1` for `s < 0`).  Hence

`∫_{‖ξ‖≤2Λ} ‖𝓕φ‖² ≤ M^{|s|} ∫_{‖ξ‖≤2Λ} w^s ‖𝓕φ‖²`
`≤ M^{|s|} ‖φ‖²_{H^s}`,

and Cauchy–Schwarz on the band turns the `L¹` Bernstein bound into the
`H^s → C^m` bound with constant `(2π·2Λ)^k · (vol(ball) · M^{|s|})^{1/2}`.
No band-limited Bernstein inequality beyond the Fourier representation is used,
and in particular no Young inequality for convolutions. -/

/-- The maximum of the Sobolev weight on the band `‖ξ‖ ≤ 2Λ`. -/
private noncomputable def bandWeightMax (Λ : ℝ) : ℝ := 1 + (2 * Real.pi * (2 * Λ)) ^ 2

/-- The Sobolev weight is at most `bandWeightMax Λ` on the ball of radius `2Λ`. -/
private theorem bandWeight_le_max {d : ℕ} {Λ : ℝ} {ξ : Space d}
    (hξ : ξ ∈ Metric.ball (0 : Space d) (2 * Λ)) :
    1 + (2 * Real.pi * ‖ξ‖) ^ 2 ≤ bandWeightMax Λ := by
  rw [Metric.mem_ball, dist_zero_right] at hξ
  have hle : ‖ξ‖ ≤ 2 * Λ := hξ.le
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h1 : 2 * Real.pi * ‖ξ‖ ≤ 2 * Real.pi * (2 * Λ) :=
    mul_le_mul_of_nonneg_left hle hpi
  have h2 : (0 : ℝ) ≤ 2 * Real.pi * ‖ξ‖ := mul_nonneg hpi (norm_nonneg _)
  rw [bandWeightMax]
  nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖), sq_nonneg (2 * Real.pi * (2 * Λ))]

/-- The maximum of the weight on the band is at least one. -/
private theorem one_le_bandWeightMax (Λ : ℝ) : 1 ≤ bandWeightMax Λ := by
  rw [bandWeightMax]
  nlinarith [sq_nonneg (2 * Real.pi * (2 * Λ))]

/-- **The weight comparison in every order.**  On the band `‖ξ‖ ≤ 2Λ`, with
`M = bandWeightMax Λ` the maximum of the weight there,
`1 ≤ M^{|s|} · w(ξ)^s`. -/
private theorem one_le_max_pow_mul_weight {d : ℕ} {Λ : ℝ} (s : ℝ) {ξ : Space d}
    (hξ : ξ ∈ Metric.ball (0 : Space d) (2 * Λ)) :
    1 ≤ bandWeightMax Λ ^ |s| * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
  have hM1 : 1 ≤ bandWeightMax Λ := one_le_bandWeightMax Λ
  have hw1 : 1 ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hwM : 1 + (2 * Real.pi * ‖ξ‖) ^ 2 ≤ bandWeightMax Λ := bandWeight_le_max hξ
  by_cases hs : 0 ≤ s
  · rw [abs_of_nonneg hs]
    have h1 := Real.one_le_rpow hM1 hs
    have h2 := Real.one_le_rpow hw1 hs
    nlinarith [h1, h2]
  · have hs' : s < 0 := lt_of_not_ge hs
    rw [abs_of_neg hs']
    have hdiv : 1 ≤ bandWeightMax Λ / (1 + (2 * Real.pi * ‖ξ‖) ^ 2) :=
      (one_le_div (by linarith)).mpr hwM
    have hstep : 1 ≤ (bandWeightMax Λ / (1 + (2 * Real.pi * ‖ξ‖) ^ 2)) ^ (-s) :=
      Real.one_le_rpow hdiv (by linarith)
    have hrewrite : (bandWeightMax Λ / (1 + (2 * Real.pi * ‖ξ‖) ^ 2)) ^ (-s)
        = bandWeightMax Λ ^ (-s) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
      rw [Real.div_rpow (le_of_lt (lt_of_lt_of_le zero_lt_one hM1)) (by linarith),
        Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2),
        div_eq_mul_inv, inv_inv]
    rwa [hrewrite] at hstep

/-- **The `L²` mass on the band, in every order.**  The weighted Cauchy-Schwarz
comparison of the previous section, with the weight lower bound
`1 ≤ M^{|s|} w^s` instead of monotonicity in `s`. -/
private theorem setLIntegral_ball_sq_le {d : ℕ} {Λ : ℝ} (s : ℝ) (φ : Space d → ℝ) :
    ∫⁻ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ENNReal.ofReal (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
      ≤ ENNReal.ofReal (bandWeightMax Λ ^ |s|) * sobolevNormSq d s φ := by
  have hM1 : 1 ≤ bandWeightMax Λ := one_le_bandWeightMax Λ
  have hpt : ∀ ξ ∈ Metric.ball (0 : Space d) (2 * Λ),
      ENNReal.ofReal (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
        ≤ ENNReal.ofReal (bandWeightMax Λ ^ |s|) *
            ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ hξ
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (le_trans zero_le_one hM1) _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := one_le_max_pow_mul_weight (d := d) s hξ
    nlinarith [sq_nonneg ‖𝓕 (fun x => (φ x : ℂ)) ξ‖, h1]
  calc ∫⁻ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ENNReal.ofReal (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ in Metric.ball (0 : Space d) (2 * Λ),
          ENNReal.ofReal (bandWeightMax Λ ^ |s|) *
            ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
        exact hpt ξ hξ
    _ = ENNReal.ofReal (bandWeightMax Λ ^ |s|) *
          ∫⁻ ξ in Metric.ball (0 : Space d) (2 * Λ),
            ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (bandWeightMax Λ ^ |s|) * sobolevNormSq d s φ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sobolevNormSq]
        exact setLIntegral_le_lintegral _ _

/-- **Cauchy–Schwarz on the band, against the band `L²` mass.**  The same
Hölder step as `integral_norm_le_sqrt_volume_mul_sqrt_sq`, but keeping the `L²`
integral on the ball rather than passing to the full-space one; this is what the
negative-order case needs, since there the weight is *larger* outside the band. -/
private theorem integral_norm_ball_le_sqrt_volume_mul_sqrt_ball_sq {d : ℕ} {f : Space d → ℂ}
    (hf : MemLp f 2 volume) (Λ : ℝ) :
    ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖f ξ‖
      ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
        * Real.sqrt (∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖f ξ‖ ^ 2) := by
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
  have hleft : ∫ a, ‖f a‖ * (1 : ℝ)
        ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = ∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ := by
    simp only [mul_one]
  have hA : ∫ a, ‖f a‖ ^ (2 : ℝ) ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = ∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => Real.rpow_two _)
  have hB : ∫ a, (1 : ℝ) ^ (2 : ℝ) ∂(volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      = (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal := by
    simp only [Real.one_rpow, integral_const, Measure.restrict_apply_univ, smul_eq_mul,
      mul_one, Measure.real]
  rw [hleft, hA, hB] at hholder
  calc ∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖
      ≤ (∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2) ^ (1 / 2 : ℝ)
          * (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal ^ (1 / 2 : ℝ) := hholder
    _ = Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
          * Real.sqrt (∫ a in Metric.ball (0 : Space d) (2 * Λ), ‖f a‖ ^ 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, mul_comm]

/-- **The band-limited `C^m` bound in every Sobolev order.**  For every real `s`,
every cutoff `Λ > 0` and every order `k`, the `k`-th derivative of the truncation
`P_Λ` of a test function is uniformly bounded over the `H^s` unit ball.  This
removes the `s ≥ 0` restriction of `exists_iteratedFDeriv_bandTrunc_le_Hs`.  The
constant is `C₀ · (vol(ball 0 (2Λ)) · M^{|s|})^{1/2}`, `C₀` the `L¹` Bernstein
constant and `M = bandWeightMax Λ` the maximum of the Sobolev weight on the band;
no band-limited Bernstein inequality beyond the Fourier representation is used. -/
theorem exists_iteratedFDeriv_bandTrunc_le_Hs_all {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ)
    (s : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ) (x : Space d),
      sobolevNormSq d s φ ≤ 1 →
        ‖iteratedFDeriv ℝ k
            (fun y => bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y) x‖
          ≤ C := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_iteratedFDeriv_bandTrunc_le (d := d) Λ hΛ k
  have hM1 : 1 ≤ bandWeightMax Λ := one_le_bandWeightMax Λ
  have hMnn : (0 : ℝ) ≤ bandWeightMax Λ ^ |s| := Real.rpow_nonneg (le_trans zero_le_one hM1) _
  have hvol : (0 : ℝ) ≤ (volume (Metric.ball (0 : Space d) (2 * Λ))).toReal :=
    ENNReal.toReal_nonneg
  refine ⟨C₀ * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal
    * bandWeightMax Λ ^ |s|) + 1, by positivity, fun φ hcont hcs x hnorm => ?_⟩
  have hint : Integrable
      (fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) volume := by
    have hmem : MemLp
        (fun ξ : Space d => 𝓕 (realToComplexSchwartz d φ hcont hcs) ξ) 2 volume :=
      (𝓕 (realToComplexSchwartz d φ hcont hcs)).memLp 2 volume
    have h2 : Integrable
        (fun ξ : Space d => ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    refine h2.congr ?_
    filter_upwards with ξ
    rw [fourier_realToComplexSchwartz d φ hcont hcs]
  have heq : (∫⁻ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ENNReal.ofReal (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)).toReal
      = ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
          ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Metric.ball (0 : Space d) (2 * Λ)))
      (f := fun ξ : Space d => ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)
      hint.integrableOn (Filter.Eventually.of_forall fun ξ => sq_nonneg _)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun ξ => sq_nonneg _)
  have hsq : ∫ ξ in Metric.ball (0 : Space d) (2 * Λ), ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2
      ≤ bandWeightMax Λ ^ |s| := by
    rw [← heq]
    refine (ENNReal.toReal_mono ?_ (setLIntegral_ball_sq_le (d := d) (Λ := Λ) s φ)).trans ?_
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top hnorm)
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMnn]
      calc bandWeightMax Λ ^ |s| * (sobolevNormSq d s φ).toReal
          ≤ bandWeightMax Λ ^ |s| * 1 :=
            mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ENNReal.one_ne_top hnorm) hMnn
        _ = bandWeightMax Λ ^ |s| := mul_one _
  have hcongr : ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2
      = ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
          ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with ξ _
    rw [fourier_realToComplexSchwartz d φ hcont hcs]
  have hL1 : ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖
      ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal
          * bandWeightMax Λ ^ |s|) := by
    have hb := integral_norm_ball_le_sqrt_volume_mul_sqrt_ball_sq
      ((𝓕 (realToComplexSchwartz d φ hcont hcs)).memLp 2 volume) Λ
    have h2 : Real.sqrt (∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2)
        ≤ Real.sqrt (bandWeightMax Λ ^ |s|) := by
      rw [← hcongr]
      exact Real.sqrt_le_sqrt hsq
    calc ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
          ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖
        ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
            * Real.sqrt (∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
                ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖ ^ 2) := hb
      _ ≤ Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal)
            * Real.sqrt (bandWeightMax Λ ^ |s|) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal
            * bandWeightMax Λ ^ |s|) := (Real.sqrt_mul hvol (bandWeightMax Λ ^ |s|)).symm
  refine (hbound (realToComplexSchwartz d φ hcont hcs) x).trans ?_
  calc C₀ * ∫ ξ in Metric.ball (0 : Space d) (2 * Λ),
        ‖𝓕 (realToComplexSchwartz d φ hcont hcs) ξ‖
      ≤ C₀ * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal
          * bandWeightMax Λ ^ |s|) := mul_le_mul_of_nonneg_left hL1 hC₀
    _ ≤ C₀ * Real.sqrt ((volume (Metric.ball (0 : Space d) (2 * Λ))).toReal
          * bandWeightMax Λ ^ |s|) + 1 := le_add_of_nonneg_right zero_le_one

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

/-- `BandLimitedCmBound` holds for every cutoff and **every** real order `s`. -/
theorem bandLimitedCmBound_holds_all {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) (s : ℝ) :
    BandLimitedCmBound d Λ hΛ.ne' s :=
  fun k => exists_iteratedFDeriv_bandTrunc_le_Hs_all Λ hΛ s k

end LatticeProb.Sobolev
