import LatticeProb.LQG.LQGMeasure
import LatticeProb.Gauss.CircleAverageApprox

/-!
# Dilation of the circle-average approximations of Gaussian multiplicative chaos

For circle averages `h : ℝ → ℂ → ℝ` (`h r z` is the average of the field over the circle of radius `r`
about `z`) and `c > 0`, the Lebesgue-density approximation `lqgApprox γ h (c ε) = (c ε)^{γ²/2} e^{γ h (c ε) z} dz`
is the image under `w ↦ c w` of the approximation of the dilated circle averages `(r, w) ↦ h (c r) (c w)` at scale
`ε`, up to the constant `c^{2 + γ²/2}`.

For the field `h = h^ℂ - α log |·|` with a logarithmic singularity at the origin this gives the exact scaling law
`lqgApprox γ (fieldCircleAverage α hcirc) (c ε) = c^{γ (Q - α)} e^{γ h^ℂ_c(0)} · (image of the approximation of
the recentred dilated field `h^ℂ(c ·) - h^ℂ_c(0)` at scale `ε`)`, `Q = 2/γ + γ/2`, since `γ Q = 2 + γ²/2`.

## Main results

* `lqgApprox_dilation`, `integral_lqgApprox_dilation`, `lqgApprox_dilation_ball`: the identity for general circle
  averages, as measures, as integrals, and for the masses of balls and annuli about the origin.
* `fieldCircleAverage_dilate`: `h_{cr}(cz) = h^{rec}_r(z) + h^ℂ_c(0) - α log c` for the singular field.
* `lqgApprox_fieldCircleAverage_dilation` and `lqgApprox_fieldCircleAverage_dilation_ball`: the scaling law with
  exponent `σ = γ (Q - α)`, in particular the mass of `B_c(0)` at scale `c` equals
  `c^σ e^{γ h^ℂ_c(0)}` times the mass of `B_1(0)` at scale `1` of the recentred dilated field.
* `lqgApprox_fieldCircleAverage_dyadic`: the same at dyadic scales, `dyadicScale (j + n) = dyadicScale j * dyadicScale n`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- The dilated circle averages `(r, w) ↦ h (c r) (c w)`. -/
noncomputable def dilateField (c : ℝ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r w => h (c * r) ((c : ℂ) * w)

/-- The dilated circle averages recentred at the circle of radius `c` about the origin:
`(r, w) ↦ h (c r) (c w) - h c 0`. -/
noncomputable def dilateRecentre (c : ℝ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r w => h (c * r) ((c : ℂ) * w) - h c 0

/-- Multiplication by a nonzero real number is a measurable embedding of `ℂ`. -/
theorem measurableEmbedding_mul_ofReal {c : ℝ} (hc : c ≠ 0) :
    MeasurableEmbedding fun w : ℂ => (c : ℂ) * w :=
  (Homeomorph.mulLeft₀ (c : ℂ) (Complex.ofReal_ne_zero.2 hc)).measurableEmbedding

/-- Change of variables for the Lebesgue integral under the dilation `w ↦ c w` of the plane. -/
theorem lintegral_dilate (g : ℂ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∫⁻ z, g z = ENNReal.ofReal (c ^ 2) * ∫⁻ w, g ((c : ℂ) * w) := by
  have he := measurableEmbedding_mul_ofReal hc.ne'
  have hmap : (volume : Measure ℂ).map (fun w : ℂ => (c : ℂ) * w) =
      ENNReal.ofReal (c ^ 2)⁻¹ • volume := by
    have h := Measure.map_addHaar_smul (volume : Measure ℂ) hc.ne'
    simp only [Complex.finrank_real_complex, abs_inv, abs_pow, abs_of_pos hc] at h
    have : (fun w : ℂ => (c : ℂ) * w) = fun w : ℂ => c • w := by
      funext w; simp [Complex.real_smul]
    rw [this, h]
  rw [← he.lintegral_map, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.mul_inv_cancel, one_mul]
  · simp [hc.ne']
  · exact ENNReal.ofReal_ne_top

/-- Adding a constant `a` to the circle averages multiplies the approximation by `e^{γ a}`. -/
theorem lqgApprox_add_const (γ : ℝ) (h : ℝ → ℂ → ℝ) (a ε : ℝ) :
    lqgApprox γ (fun s z => h s z + a) ε = ENNReal.ofReal (Real.exp (γ * a)) • lqgApprox γ h ε := by
  simp only [lqgApprox]
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
  ring_nf

/-- The approximation at scale `ε` only depends on the circle averages at scale `ε`. -/
theorem lqgApprox_congr (γ : ℝ) {h h' : ℝ → ℂ → ℝ} {ε : ℝ} (hh : ∀ z, h ε z = h' ε z) :
    lqgApprox γ h ε = lqgApprox γ h' ε := by
  simp only [lqgApprox, hh]

/-- **Dilation of the approximation.** For `c > 0` and `ε ≥ 0`, the approximation at scale `c ε` is the image,
under `w ↦ c w`, of the approximation of the dilated circle averages at scale `ε`, times `c^{2 + γ²/2}`. -/
theorem lqgApprox_dilation (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) :
    lqgApprox γ h (c * ε) = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) •
      (lqgApprox γ (dilateField c h) ε).map (fun w : ℂ => (c : ℂ) * w) := by
  have he := measurableEmbedding_mul_ofReal hc.ne'
  ext S hS
  rw [Measure.smul_apply, he.map_apply, smul_eq_mul]
  simp only [lqgApprox]
  rw [withDensity_apply _ hS, withDensity_apply _ (he.measurable hS), ← lintegral_indicator hS,
    lintegral_dilate _ hc, ← lintegral_indicator (he.measurable hS)]
  have hint : ∫⁻ w, S.indicator (fun z => ENNReal.ofReal ((c * ε) ^ (γ ^ 2 / 2) *
        Real.exp (γ * h (c * ε) z))) ((c : ℂ) * w) =
      ENNReal.ofReal (c ^ (γ ^ 2 / 2)) * ∫⁻ w, ((fun w : ℂ => (c : ℂ) * w) ⁻¹' S).indicator
        (fun w => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * dilateField c h ε w))) w := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun w => ?_
    by_cases hw : (c : ℂ) * w ∈ S
    · have hw' : w ∈ (fun w : ℂ => (c : ℂ) * w) ⁻¹' S := hw
      rw [indicator_of_mem hw, indicator_of_mem hw']
      simp only [dilateField]
      rw [Real.mul_rpow hc.le hε, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · have hw' : w ∉ (fun w : ℂ => (c : ℂ) * w) ⁻¹' S := hw
      rw [indicator_of_notMem hw, indicator_of_notMem hw', mul_zero]
  rw [hint, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_two c,
    ← Real.rpow_add hc]

/-- **Dilation of the approximation, integrals.** -/
theorem integral_lqgApprox_dilation (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ h (c * ε)) =
      c ^ (2 + γ ^ 2 / 2) * ∫ w, f ((c : ℂ) * w) ∂(lqgApprox γ (dilateField c h) ε) := by
  rw [lqgApprox_dilation γ h hc hε, integral_smul_measure,
    (measurableEmbedding_mul_ofReal hc.ne').integral_map, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-- The preimage of the ball about the origin under the dilation `w ↦ c w`. -/
theorem preimage_mul_ofReal_ball {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    (fun w : ℂ => (c : ℂ) * w) ⁻¹' ball (0 : ℂ) (c * ρ) = ball (0 : ℂ) ρ := by
  ext w
  simp [abs_of_pos hc, hc]

/-- The preimage of the closed ball about the origin under the dilation `w ↦ c w`. -/
theorem preimage_mul_ofReal_closedBall {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    (fun w : ℂ => (c : ℂ) * w) ⁻¹' closedBall (0 : ℂ) (c * ρ) = closedBall (0 : ℂ) ρ := by
  ext w
  simp [abs_of_pos hc, hc]

/-- **Dilation of the approximation, sets.** For a measurable set `S`, the mass of `S` at scale `c ε` is
`c^{2 + γ²/2}` times the mass of the preimage of `S` under `w ↦ c w` at scale `ε` for the dilated circle averages. -/
theorem lqgApprox_dilation_apply (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (S : Set ℂ) :
    lqgApprox γ h (c * ε) S = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
      lqgApprox γ (dilateField c h) ε ((fun w : ℂ => (c : ℂ) * w) ⁻¹' S) := by
  rw [lqgApprox_dilation γ h hc hε, Measure.smul_apply,
    (measurableEmbedding_mul_ofReal hc.ne').map_apply, smul_eq_mul]

/-- **Dilation of the approximation, balls.** -/
theorem lqgApprox_dilation_ball (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (ρ : ℝ) :
    lqgApprox γ h (c * ε) (ball 0 (c * ρ)) = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
      lqgApprox γ (dilateField c h) ε (ball 0 ρ) := by
  rw [lqgApprox_dilation_apply γ h hc hε _, preimage_mul_ofReal_ball hc]

/-- **Dilation of the approximation, closed balls.** -/
theorem lqgApprox_dilation_closedBall (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (ρ : ℝ) :
    lqgApprox γ h (c * ε) (closedBall 0 (c * ρ)) = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
      lqgApprox γ (dilateField c h) ε (closedBall 0 ρ) := by
  rw [lqgApprox_dilation_apply γ h hc hε _,
    preimage_mul_ofReal_closedBall hc]

/-- **Dilation of the approximation, annuli.** The mass of the annulus `B_{c b}(0) \ B_{c a}(0)`. -/
theorem lqgApprox_dilation_annulus (γ : ℝ) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (a b : ℝ) :
    lqgApprox γ h (c * ε) (ball 0 (c * b) \ ball 0 (c * a)) = ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2)) *
      lqgApprox γ (dilateField c h) ε (ball 0 b \ ball 0 a) := by
  rw [lqgApprox_dilation_apply γ h hc hε _,
    preimage_sdiff, preimage_mul_ofReal_ball hc, preimage_mul_ofReal_ball hc]

/-- **Circle averages of the singular field under dilation.** For `c, r > 0`,
`h_{c r}(c z) = h^{rec}_r(z) + h^ℂ_c(0) - α log c`, where `h^{rec} = h^ℂ(c ·) - h^ℂ_c(0)`. -/
theorem fieldCircleAverage_dilate (α : ℝ) (hcirc : ℝ → ℂ → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (z : ℂ) :
    fieldCircleAverage α hcirc (c * r) ((c : ℂ) * z) =
      fieldCircleAverage α (dilateRecentre c hcirc) r z + (hcirc c 0 - α * Real.log c) := by
  have h1 : ∀ (s : ℝ) (x : ℂ), 0 < s →
      Real.circleAverage (fun y : ℂ => Real.log ‖y‖) x s = Real.log (max s ‖x‖) := by
    intro s x hs
    simpa only [sub_zero] using circleAverage_log_norm_sub_eq_log_max hs x 0
  simp only [fieldCircleAverage, dilateRecentre]
  rw [h1 _ _ (mul_pos hc hr), h1 _ _ hr, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
    ← mul_max_of_nonneg _ _ hc.le, Real.log_mul hc.ne' (lt_of_lt_of_le hr (le_max_left _ _)).ne']
  ring

/-- `γ Q = 2 + γ²/2` for `Q = 2/γ + γ/2`. -/
theorem mul_lqgQ {γ : ℝ} (hγ : γ ≠ 0) : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
  unfold lqgQ
  field_simp

/-- **Scaling law of the approximation of the singular field.** For `γ ≠ 0`, `c > 0` and `ε > 0`,
`lqgApprox γ (fieldCircleAverage α hcirc) (c ε) = c^{γ (Q - α)} e^{γ h^ℂ_c(0)} ·
(lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε)` pushed forward under `w ↦ c w`. -/
theorem lqgApprox_fieldCircleAverage_dilation {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) (hcirc : ℝ → ℂ → ℝ)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    lqgApprox γ (fieldCircleAverage α hcirc) (c * ε) =
      ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0)) •
        (lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε).map
          (fun w : ℂ => (c : ℂ) * w) := by
  have hshift : lqgApprox γ (dilateField c (fieldCircleAverage α hcirc)) ε =
      ENNReal.ofReal (Real.exp (γ * (hcirc c 0 - α * Real.log c))) •
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε := by
    rw [← lqgApprox_add_const]
    exact lqgApprox_congr γ fun z => fieldCircleAverage_dilate α hcirc hc hε z
  have key : c ^ (2 + γ ^ 2 / 2) * Real.exp (γ * (hcirc c 0 - α * Real.log c)) =
      c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0) := by
    have h2 : γ * (lqgQ γ - α) = 2 + γ ^ 2 / 2 - γ * α := by rw [mul_sub, mul_lqgQ hγ]
    rw [h2, Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hc, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [lqgApprox_dilation γ _ hc hε.le, hshift, Measure.map_smul, smul_smul,
    ← ENNReal.ofReal_mul (by positivity), key]
  exact (measurableEmbedding_mul_ofReal hc.ne').measurable.aemeasurable

/-- **Scaling law, sets.** -/
theorem lqgApprox_fieldCircleAverage_dilation_apply {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) (hcirc : ℝ → ℂ → ℝ)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (S : Set ℂ) :
    lqgApprox γ (fieldCircleAverage α hcirc) (c * ε) S =
      ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0)) *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε
          ((fun w : ℂ => (c : ℂ) * w) ⁻¹' S) := by
  rw [lqgApprox_fieldCircleAverage_dilation hγ α hcirc hc hε, Measure.smul_apply,
    (measurableEmbedding_mul_ofReal hc.ne').map_apply, smul_eq_mul]

/-- **Scaling law, balls.** -/
theorem lqgApprox_fieldCircleAverage_dilation_ball {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ)
    (hcirc : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (ρ : ℝ) :
    lqgApprox γ (fieldCircleAverage α hcirc) (c * ε) (ball 0 (c * ρ)) =
      ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0)) *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε (ball 0 ρ) := by
  rw [lqgApprox_fieldCircleAverage_dilation_apply hγ α hcirc hc hε, preimage_mul_ofReal_ball hc]

/-- **Scaling law, annuli.** -/
theorem lqgApprox_fieldCircleAverage_dilation_annulus {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ)
    (hcirc : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (a b : ℝ) :
    lqgApprox γ (fieldCircleAverage α hcirc) (c * ε) (ball 0 (c * b) \ ball 0 (c * a)) =
      ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0)) *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε (ball 0 b \ ball 0 a) := by
  rw [lqgApprox_fieldCircleAverage_dilation_apply hγ α hcirc hc hε, preimage_sdiff,
    preimage_mul_ofReal_ball hc, preimage_mul_ofReal_ball hc]

/-- **Scaling law, integrals.** -/
theorem integral_lqgApprox_fieldCircleAverage_dilation {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ)
    (hcirc : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α hcirc) (c * ε)) =
      c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0) *
        ∫ w, f ((c : ℂ) * w) ∂(lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) ε) := by
  rw [lqgApprox_fieldCircleAverage_dilation hγ α hcirc hc hε, integral_smul_measure,
    (measurableEmbedding_mul_ofReal hc.ne').integral_map, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-- **Core identity.** The mass of `B_c(0)` at scale `c` of the singular field is
`c^{γ (Q - α)} e^{γ h^ℂ_c(0)}` times the mass of `B_1(0)` at scale `1` of the recentred dilated field. -/
theorem lqgApprox_fieldCircleAverage_core {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) (hcirc : ℝ → ℂ → ℝ) {c : ℝ}
    (hc : 0 < c) :
    lqgApprox γ (fieldCircleAverage α hcirc) c (ball 0 c) =
      ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc c 0)) *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre c hcirc)) 1 (ball 0 1) := by
  simpa using lqgApprox_fieldCircleAverage_dilation_ball hγ α hcirc hc one_pos 1

/-- `2^{-(j + n)} = 2^{-j} 2^{-n}`. -/
theorem dyadicScale_add (j n : ℕ) : dyadicScale (j + n) = dyadicScale j * dyadicScale n := by
  simp only [dyadicScale, pow_add]

/-- **Scaling law at dyadic scales.** With `c = 2^{-j}`, the approximation at the dyadic scale `2^{-(j+n)}` on the
ball `B_{2^{-j} ρ}(0)` equals `2^{-jσ} e^{γ h^ℂ_{2^{-j}}(0)}` times the approximation at the scale `2^{-n}` of the
recentred dilated field on `B_ρ(0)`, `σ = γ (Q - α)`. -/
theorem lqgApprox_fieldCircleAverage_dyadic {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) (hcirc : ℝ → ℂ → ℝ)
    (j n : ℕ) (ρ : ℝ) :
    lqgApprox γ (fieldCircleAverage α hcirc) (dyadicScale (j + n)) (ball 0 (dyadicScale j * ρ)) =
      ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc (dyadicScale j) 0)) *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre (dyadicScale j) hcirc)) (dyadicScale n)
          (ball 0 ρ) := by
  rw [dyadicScale_add]
  exact lqgApprox_fieldCircleAverage_dilation_ball hγ α hcirc (by unfold dyadicScale; positivity)
    (by unfold dyadicScale; positivity) ρ

end LatticeProb.LQG
