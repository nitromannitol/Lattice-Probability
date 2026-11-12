/-
Copyright (c) 2026. All rights reserved.
-/
import LatticeProb.LQG.LQGCoordChangeFixed
import LatticeProb.LQG.LQGDyadicScaling

/-!
# Dilation of a whole-plane GFF and of its LQG measure by a power of two

Let `(hC, hcirc)` be a whole-plane GFF, `μ` its γ-LQG measure and `c = 2^j` with `j ∈ ℕ` (zooming out).
Put
* `dilatedPairing hC hcirc c φ = c⁻² hC (φ (· / c)) - h_c(0) ∫ φ`,
* `dilatedCirc hcirc c r w = h_{c r}(c w) - h_c(0)` (the circle averages of `h(c ·) - h_c(0)`),
* `dilatedMeasure γ hcirc μ c = e^{-γ (h_c(0) + Q log c)} · (μ pushed forward by w ↦ w / c)`.

Then `(dilatedPairing, dilatedCirc)` is again a whole-plane GFF, `dilatedMeasure` is its γ-LQG measure and,
almost surely,
  `μ.map (· / c) = c^{2 + γ²/2} e^{γ h_c(0)} · dilatedMeasure`
(Duplantier-Sheffield 2011, Proposition 2.1, for the map `x ↦ x / c`).  All witnesses are explicit, unlike
`exists_coordChange_of_tendsto`.  The integral form is `ae_lintegral_eq_dilationFactor_mul`:
`∫⁻ F dμ = c^{2 + γ²/2} e^{γ h_c(0)} ∫⁻ F(c w) d(dilatedMeasure)(w)`.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace DyadicDilation

/-- The pairings of the dilated field `h(c ·) - h_c(0)`: `φ ↦ c⁻² hC(φ(· / c)) - h_c(0) ∫ φ`. -/
noncomputable def dilatedPairing {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℝ) :
    Ω → (ℂ → ℝ) → ℝ :=
  fun ω φ => (c ^ 2)⁻¹ * hC ω (fun y => φ (y / (c : ℂ))) - hcirc ω c 0 * ∫ x, φ x

/-- The circle averages of the dilated field `h(c ·) - h_c(0)`: `(r, w) ↦ h_{c r}(c w) - h_c(0)`. -/
def dilatedCirc {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (c : ℝ) : Ω → ℝ → ℂ → ℝ :=
  fun ω r w => hcirc ω (c * r) ((c : ℂ) * w) - hcirc ω c 0

/-- The factor `c^{2 + γ²/2} e^{γ x}` of the scaling relation (`x` is the circle average of the field
at scale `c` about the origin). -/
noncomputable def dilationFactor (γ c x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c ^ (2 + γ ^ 2 / 2) * Real.exp (γ * x))

/-- The γ-LQG measure of the dilated field, as the normalized pushforward of `μ` by `w ↦ w / c`. -/
noncomputable def dilatedMeasure {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (c : ℝ) : Ω → Measure ℂ :=
  fun ω => ENNReal.ofReal (Real.exp (γ * -(hcirc ω c 0 + lqgQ γ * Real.log c))) •
    (μ ω).map (fun x => x / (c : ℂ))

theorem dilationFactor_ne_zero (γ c x : ℝ) (hc : 0 < c) : dilationFactor γ c x ≠ 0 :=
  (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem dilationFactor_ne_top (γ c x : ℝ) : dilationFactor γ c x ≠ ∞ := ENNReal.ofReal_ne_top

/-- The scaling factor equals `e^{γ d}` with `d = h_c(0) + Q log c`. -/
theorem dilationFactor_eq {γ : ℝ} (hγ : 0 < γ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    dilationFactor γ c x = ENNReal.ofReal (Real.exp (γ * (x + lqgQ γ * Real.log c))) := by
  unfold dilationFactor
  congr 1
  rw [mul_add, Real.exp_add, LQGCoordChangeFixed.exp_mul_lqgQ_log hγ.ne' hc,
    Real.rpow_add hc, Real.rpow_two]
  ring

/-- Convergence along the scales `2^j 2^{-k}` follows from convergence along `2^{-k}`. -/
theorem tendsto_integral_lqgApprox_two_pow_mul {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : IsLQGLimit γ h m) (j : ℕ) (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ h ((2 : ℝ) ^ j * dyadicScale k))) atTop
      (𝓝 (∫ x, f x ∂m)) := by
  rw [← tendsto_add_atTop_iff_nat j]
  have hk : ∀ k : ℕ, (2 : ℝ) ^ j * dyadicScale (k + j) = dyadicScale k := by
    intro k
    unfold dyadicScale
    have h1 : (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j = 1 := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ (k + j)
        = ((2 : ℝ) ^ j * (2 : ℝ)⁻¹ ^ j) * (2 : ℝ)⁻¹ ^ k := by rw [pow_add]; ring
      _ = (2 : ℝ)⁻¹ ^ k := by rw [h1, one_mul]
  simp_rw [hk]
  exact hm.tendsto_integral f hf hfc

/-- **Dilation, explicit form.** Under the vague-limit hypothesis `hid` along the scales `c 2^{-k}`. -/
theorem dilation_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) {c : ℝ} (hc : 0 < c)
    (hid : ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ (hcirc ω) (c * dyadicScale k))) atTop
        (𝓝 (∫ x, f x ∂(μ ω)))) :
    IsWholePlaneGFF P (dilatedPairing hC hcirc c) (dilatedCirc hcirc c) ∧
    IsLQGMeasure P γ (dilatedCirc hcirc c) (dilatedMeasure γ hcirc μ c) ∧
    ∀ᵐ ω ∂P, (μ ω).map (fun x => x / (c : ℂ)) =
      dilationFactor γ c (hcirc ω c 0) • dilatedMeasure γ hcirc μ c ω := by
  have hnr : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hG' := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG (c : ℂ)
    (Complex.ofReal_ne_zero.2 hc.ne') 0
  simp only [hnr, add_zero, sub_zero] at hG'
  refine ⟨hG', ?_, ?_⟩
  · set d : Ω → ℝ := fun ω => hcirc ω c 0 + lqgQ γ * Real.log c with hd
    filter_upwards [hμ, hid] with ω hω hidω
    have := hω.isLocallyFiniteMeasure
    have h1 := LQGMeasureNonatomicMass.isLQGLimit_add_const
      (LQGCoordChangeFixed.isLQGLimit_dilate_translate hγ.ne' hc 0 hidω) (-d ω)
    have heq : (fun ε u => hcirc ω (c * ε) ((c : ℂ) * u + 0) + lqgQ γ * Real.log c + -d ω) =
        dilatedCirc hcirc c ω := by
      funext ε u; simp only [hd, dilatedCirc, add_zero]; ring
    rw [heq] at h1
    simp only [sub_zero] at h1
    exact h1
  · filter_upwards with ω
    unfold dilatedMeasure
    rw [smul_smul, dilationFactor_eq hγ hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, mul_neg, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_smul]

/-- **Dilation by `2^j`.** -/
theorem dilation_two_pow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) :
    IsWholePlaneGFF P (dilatedPairing hC hcirc ((2 : ℝ) ^ j)) (dilatedCirc hcirc ((2 : ℝ) ^ j)) ∧
    IsLQGMeasure P γ (dilatedCirc hcirc ((2 : ℝ) ^ j))
      (dilatedMeasure γ hcirc μ ((2 : ℝ) ^ j)) ∧
    ∀ᵐ ω ∂P, (μ ω).map (fun x => x / (((2 : ℝ) ^ j : ℝ) : ℂ)) =
      dilationFactor γ ((2 : ℝ) ^ j) (hcirc ω ((2 : ℝ) ^ j) 0) •
        dilatedMeasure γ hcirc μ ((2 : ℝ) ^ j) ω :=
  dilation_of_tendsto hγ hG hμ (by positivity) (by
    filter_upwards [hμ] with ω hω f hf hfc
    exact tendsto_integral_lqgApprox_two_pow_mul hω j f hf hfc)

/-- **Integral form of the scaling relation.** For measurable `F : ℂ → [0, ∞]`,
`∫⁻ F dμ = c^{2 + γ²/2} e^{γ h_c(0)} ∫⁻ F(c w) d(dilatedMeasure)(w)`. -/
theorem lintegral_eq_dilationFactor_mul_of_map_eq {μ ν : Measure ℂ} {c : ℝ} (hc : 0 < c) {K : ℝ≥0∞}
    (hmap : μ.map (fun x => x / (c : ℂ)) = K • ν) {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂μ = K * ∫⁻ w, F ((c : ℂ) * w) ∂ν := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hm1 : Measurable fun x : ℂ => x / (c : ℂ) := by fun_prop
  have hm2 : Measurable fun w : ℂ => F ((c : ℂ) * w) := hF.comp (by fun_prop)
  have h1 : ∫⁻ w, F ((c : ℂ) * w) ∂(μ.map (fun x => x / (c : ℂ))) = ∫⁻ x, F x ∂μ := by
    rw [lintegral_map hm2 hm1]
    congr 1
    funext x
    congr 1
    field_simp
  rw [← h1, hmap, lintegral_smul_measure, smul_eq_mul]

end DyadicDilation

end LatticeProb.LQG
