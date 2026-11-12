import LatticeProb.LQG.LQGCoordChangeFixed
import LatticeProb.LQG.GMCAffineCovariance
import LatticeProb.LQG.LQGMeasureDerived

/-! # Dyadic scaling of the LQG measure about a point

Let `μ` be the γ-LQG measure of the circle-average field `hcirc`, let `z ∈ ℂ` and `j ∈ ℕ`, and put `r = 2^{-j}`.
Recentre and dilate the field: `h'_ε(w) = h_{r ε}(r w + z) - h_r(z)`. If `μ'` is the γ-LQG measure of `h'`, then
almost surely
  `μ = r^{γ Q} e^{γ h_r(z)} · (μ' pushed forward by w ↦ r w + z)`,  `γ Q = 2 + γ²/2`
(Duplantier-Sheffield 2011, Proposition 2.1, for the map `x ↦ (x - z)/r`). This is the exact scaling relation
behind the multifractal moment estimates for the masses of small balls: for `0 < ρ`
  `μ(B(z, r ρ)) = r^{γ Q} e^{γ h_r(z)} μ'(B(0, ρ))`.

The statements are deterministic (almost sure, without any Gaussianity); the recentred field is again a whole-plane
GFF when `hcirc` is one.

Main results:
* `isWholePlaneGFF_recentredField`: the recentred field is a whole-plane GFF.
* `ae_map_eq_smul`: the pushforward form of the scaling relation.
* `ae_eq_smul_map`: `μ = c • (μ'.map (w ↦ r w + z))`.
* `ae_integral_eq`, `ae_measure_ball_eq`: the integral and ball-mass forms.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace LQGDyadicScaling

/-- The circle averages of the field recentred at `z` and dilated by `2^{-j}`:
`(ε, w) ↦ h_{2^{-j} ε}(2^{-j} w + z) - h_{2^{-j}}(z)`. -/
noncomputable def recentredField {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (j : ℕ) (z : ℂ) :
    Ω → ℝ → ℂ → ℝ :=
  fun ω ε w => hcirc ω (dyadicScale j * ε) ((dyadicScale j : ℂ) * w + z) - hcirc ω (dyadicScale j) z

/-- The scaling factor `r^{2 + γ²/2} e^{γ x}` (`r = 2^{-j}`, `x` the circle average of the field at scale `r`). -/
noncomputable def dyadicFactor (γ : ℝ) (j : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (dyadicScale j ^ (2 + γ ^ 2 / 2) * Real.exp (γ * x))

theorem dyadicScale_pos' (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale; positivity

theorem dyadicFactor_ne_zero (γ : ℝ) (j : ℕ) (x : ℝ) : dyadicFactor γ j x ≠ 0 := by
  unfold dyadicFactor
  have := dyadicScale_pos' j
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem dyadicFactor_ne_top (γ : ℝ) (j : ℕ) (x : ℝ) : dyadicFactor γ j x ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The recentred and dilated field of a whole-plane GFF is a whole-plane GFF. -/
theorem isWholePlaneGFF_recentredField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (j : ℕ)
    (z : ℂ) : ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' (recentredField hcirc j z) := by
  have hr := dyadicScale_pos' j
  have hnr : ‖(dyadicScale j : ℂ)‖ = dyadicScale j := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hG' := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG (dyadicScale j : ℂ)
    (Complex.ofReal_ne_zero.2 hr.ne') z
  rw [hnr] at hG'
  exact ⟨_, hG'⟩

theorem dyadicScale_mul_dyadicScale (j k : ℕ) :
    dyadicScale j * dyadicScale k = dyadicScale (k + j) := by
  simp only [dyadicScale]; rw [pow_add, mul_comm]

theorem rpow_two_add_half_sq {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    r ^ (2 + γ ^ 2 / 2) = r ^ 2 * r ^ (γ ^ 2 / 2) := by
  rw [Real.rpow_add hr, Real.rpow_two]

/-- **Scaling relation, pushforward form.** If `μ` is the LQG measure of `hcirc` and `μ'` that of the recentred
field `hcirc(2^{-j} · + z) - hcirc_{2^{-j}}(z)`, then almost surely
`(μ).map ((· - z) / 2^{-j}) = 2^{-j(2 + γ²/2)} e^{γ h_{2^{-j}}(z)} μ'`. -/
theorem ae_map_eq_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') :
    ∀ᵐ ω ∂P, (μ ω).map (fun x => (x - z) / (dyadicScale j : ℂ)) =
      dyadicFactor γ j (hcirc ω (dyadicScale j) z) • μ' ω := by
  have hr := dyadicScale_pos' j
  filter_upwards [hμ, hμ'] with ω hω hω'
  have hlf := hω.isLocallyFiniteMeasure
  have hid : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ (hcirc ω) (dyadicScale j * dyadicScale k)))
        atTop (𝓝 (∫ x, f x ∂(μ ω))) := by
    intro f hf hfc
    have hA := (isLQGLimitAlong_shift_iff dyadicScale j).2
      (isLQGLimit_iff_isLQGLimitAlong_dyadic.1 hω)
    have := hA.tendsto_integral f hf hfc
    simp_rw [dyadicScale_mul_dyadicScale]
    exact this
  have h1 := LQGCoordChangeFixed.isLQGLimit_dilate_translate hγ.ne' hr z hid
  set d : ℝ := hcirc ω (dyadicScale j) z + lqgQ γ * Real.log (dyadicScale j) with hd
  have h2 := LQGMeasureNonatomicMass.isLQGLimit_add_const h1 (-d)
  have heq : (fun ε u => hcirc ω (dyadicScale j * ε) ((dyadicScale j : ℂ) * u + z) +
      lqgQ γ * Real.log (dyadicScale j) + -d) = recentredField hcirc j z ω := by
    funext ε u; simp only [hd, recentredField]; ring
  rw [heq] at h2
  have h3 := ProfileDerived.isLQGLimit_unique h2 hω'
  have hconst : ENNReal.ofReal (Real.exp (γ * d)) =
      dyadicFactor γ j (hcirc ω (dyadicScale j) z) := by
    unfold dyadicFactor
    congr 1
    rw [hd, mul_add, Real.exp_add, LQGCoordChangeFixed.exp_mul_lqgQ_log hγ.ne' hr,
      rpow_two_add_half_sq hr, mul_comm (Real.exp _)]
  rw [← h3, smul_smul, ← hconst, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    mul_neg, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_smul]

/-- The affine map `w ↦ 2^{-j} w + z` is a measurable embedding of the plane. -/
theorem measurableEmbedding_dilate (j : ℕ) (z : ℂ) :
    MeasurableEmbedding (fun w : ℂ => (dyadicScale j : ℂ) * w + z) := by
  have hr := dyadicScale_pos' j
  have hr' : (dyadicScale j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  exact ((Homeomorph.mulLeft₀ (dyadicScale j : ℂ) hr').trans (Homeomorph.addRight z))
    |>.measurableEmbedding

/-- **Scaling relation.** Almost surely, `μ = 2^{-j(2 + γ²/2)} e^{γ h_{2^{-j}}(z)} · (μ'.map (w ↦ 2^{-j} w + z))`. -/
theorem ae_eq_smul_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') :
    ∀ᵐ ω ∂P, μ ω = dyadicFactor γ j (hcirc ω (dyadicScale j) z) •
      (μ' ω).map (fun w : ℂ => (dyadicScale j : ℂ) * w + z) := by
  have hr := dyadicScale_pos' j
  have hr' : (dyadicScale j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hF := (measurableEmbedding_dilate j z).measurable
  have hT : Measurable (fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) := by fun_prop
  filter_upwards [ae_map_eq_smul hγ hμ j z hμ'] with ω hω
  ext S hS
  have hpre : (fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) ⁻¹'
      ((fun w : ℂ => (dyadicScale j : ℂ) * w + z) ⁻¹' S) = S := by
    ext x
    simp only [mem_preimage]
    rw [mul_div_cancel₀ _ hr', sub_add_cancel]
  have h1 : μ ω S = (μ ω).map (fun x : ℂ => (x - z) / (dyadicScale j : ℂ))
      ((fun w : ℂ => (dyadicScale j : ℂ) * w + z) ⁻¹' S) := by
    rw [Measure.map_apply hT (hF hS), hpre]
  rw [h1, hω, Measure.smul_apply, Measure.smul_apply, Measure.map_apply hF hS]

/-- **Integral form of the scaling relation.** Almost surely, for every function `g`,
`∫ g dμ = 2^{-j(2 + γ²/2)} e^{γ h_{2^{-j}}(z)} ∫ g(2^{-j} w + z) dμ'(w)`. -/
theorem ae_integral_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, ∫ x, g x ∂(μ ω) =
      (dyadicFactor γ j (hcirc ω (dyadicScale j) z)).toReal *
        ∫ w, g ((dyadicScale j : ℂ) * w + z) ∂(μ' ω) := by
  filter_upwards [ae_eq_smul_map hγ hμ j z hμ'] with ω hω g
  rw [hω, integral_smul_measure, (measurableEmbedding_dilate j z).integral_map, smul_eq_mul]

/-- **Ball masses.** Almost surely, for every `ρ > 0`,
`μ(B(z, 2^{-j} ρ)) = 2^{-j(2 + γ²/2)} e^{γ h_{2^{-j}}(z)} μ'(B(0, ρ))`. -/
theorem ae_measure_ball_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') :
    ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ → μ ω (ball z (dyadicScale j * ρ)) =
      dyadicFactor γ j (hcirc ω (dyadicScale j) z) * μ' ω (ball 0 ρ) := by
  have hr := dyadicScale_pos' j
  filter_upwards [ae_eq_smul_map hγ hμ j z hμ'] with ω hω ρ hρ
  have hpre : (fun w : ℂ => (dyadicScale j : ℂ) * w + z) ⁻¹' ball z (dyadicScale j * ρ) =
      ball 0 ρ := by
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  rw [hω, Measure.smul_apply, Measure.map_apply (measurableEmbedding_dilate j z).measurable
    measurableSet_ball, hpre, smul_eq_mul]

end LQGDyadicScaling

end LatticeProb.LQG
