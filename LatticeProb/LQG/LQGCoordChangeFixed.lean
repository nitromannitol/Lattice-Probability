import LatticeProb.LQG.GMCDilation
import LatticeProb.LQG.LQGMeasureNonatomicMassAffine
import LatticeProb.Gauss.GFFAffineInvariance

/-! # The LQG coordinate change for a fixed dilation and translation

For `r > 0` and `z ∈ ℂ`, the circle-average approximations of the field `h(r · + z) + Q log r` at scale `ε` are the
images of the approximations of `h` at scale `r ε` under `x ↦ (x - z) / r`:
  `lqgApprox γ (h(r ·)(r · + z) + Q log r) ε = (lqgApprox γ h (r ε)).map ((· - z) / r)`
(change of variables `x = r u + z`, `dx = r² du`, and `γ Q = 2 + γ²/2`). Hence a vague limit of the approximations
of `h` along the scales `r 2^{-k}` transfers to the dyadic LQG limit of the transformed field (Duplantier-Sheffield
2011, Proposition 2.1, for a fixed conformal map). For the whole-plane GFF this gives the coordinate change rule for
the map `x ↦ (x - z) / r`, with the recentred field `h(r · + z) - h_r(z)` (again a whole-plane GFF) and a positive
finite random constant, once the limit along `r 2^{-k}` is identified with the dyadic limit.

Main results:
* `lqgApprox_dilate_translate`: the change of variables for the approximations.
* `isLQGLimit_dilate_translate`: transfer of a vague limit along `r 2^{-k}`.
* `exists_coordChange_of_tendsto`: the coordinate change rule for a fixed `r > 0`, `z`, from the identification.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace LQGCoordChangeFixed

/-- The affine map `x ↦ (x - z) / r` as a homeomorphism of the plane. -/
noncomputable def affineHomeomorph {r : ℝ} (hr : 0 < r) (z : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.addRight (-z)).trans
    (Homeomorph.mulLeft₀ ((r : ℂ)⁻¹) (inv_ne_zero (Complex.ofReal_ne_zero.2 hr.ne')))

theorem coe_affineHomeomorph {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (affineHomeomorph hr z : ℂ → ℂ) = fun x => (x - z) / (r : ℂ) := by
  funext x
  simp only [affineHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_addRight,
    Homeomorph.coe_mulLeft₀]
  rw [div_eq_inv_mul, sub_eq_add_neg]

/-- `e^{γ Q log r} = r² r^{γ²/2}`. -/
theorem exp_mul_lqgQ_log {γ : ℝ} (hγ : γ ≠ 0) {r : ℝ} (hr : 0 < r) :
    Real.exp (γ * (lqgQ γ * Real.log r)) = r ^ 2 * r ^ (γ ^ 2 / 2) := by
  rw [← mul_assoc, mul_lqgQ hγ, mul_comm, ← Real.rpow_def_of_pos hr, Real.rpow_add hr, Real.rpow_two]

/-- **Change of variables for the approximations.** For `r > 0`, `ε ≥ 0` and `z ∈ ℂ`,
`lqgApprox γ (h(r ·)(r · + z) + Q log r) ε = (lqgApprox γ h (r ε)).map ((· - z) / r)`. -/
theorem lqgApprox_dilate_translate {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 ≤ ε) (z : ℂ) :
    lqgApprox γ (fun ε u => h (r * ε) ((r : ℂ) * u + z) + lqgQ γ * Real.log r) ε =
      (lqgApprox γ h (r * ε)).map (fun x => (x - z) / (r : ℂ)) := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hT : Measurable (fun x : ℂ => (x - z) / (r : ℂ)) := by fun_prop
  ext S hS
  rw [Measure.map_apply hT hS]
  simp only [lqgApprox]
  rw [withDensity_apply _ hS, withDensity_apply _ (hT hS), ← lintegral_indicator hS,
    ← lintegral_indicator (hT hS)]
  set F : ℂ → ℝ≥0∞ := ((fun x : ℂ => (x - z) / (r : ℂ)) ⁻¹' S).indicator
    (fun x => ENNReal.ofReal ((r * ε) ^ (γ ^ 2 / 2) * Real.exp (γ * h (r * ε) x))) with hF
  have e1 : ∫⁻ x, F x = ENNReal.ofReal (r ^ 2) * ∫⁻ w, F ((r : ℂ) * w + z) :=
    calc ∫⁻ x, F x = ∫⁻ x, F (x + z) := (lintegral_add_right_eq_self F z).symm
      _ = ENNReal.ofReal (r ^ 2) * ∫⁻ w, F ((r : ℂ) * w + z) :=
        lintegral_dilate (fun x => F (x + z)) hr
  rw [e1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext w
  have hpre : ((r : ℂ) * w + z) ∈ (fun x : ℂ => (x - z) / (r : ℂ)) ⁻¹' S ↔ w ∈ S := by
    simp only [mem_preimage, add_sub_cancel_right, mul_div_cancel_left₀ _ hr']
  by_cases hw : w ∈ S
  · rw [hF, indicator_of_mem hw, indicator_of_mem (hpre.2 hw),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hr.le hε, mul_add, Real.exp_add, exp_mul_lqgQ_log hγ hr]
    ring
  · rw [hF, indicator_of_notMem hw, indicator_of_notMem (fun h' => hw (hpre.1 h')), mul_zero]

/-- **Transfer of a vague limit.** If the approximations of `h` along the scales `r 2^{-k}` converge vaguely to a
Radon measure `m`, then `m.map ((· - z) / r)` is the dyadic LQG limit of `h(r ·)(r · + z) + Q log r`. -/
theorem isLQGLimit_dilate_translate {γ : ℝ} (hγ : γ ≠ 0) {h : ℝ → ℂ → ℝ} {m : Measure ℂ} {r : ℝ}
    (hr : 0 < r) (z : ℂ) [IsLocallyFiniteMeasure m]
    (hm : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ h (r * dyadicScale k))) atTop (𝓝 (∫ x, f x ∂m))) :
    IsLQGLimit γ (fun ε u => h (r * ε) ((r : ℂ) * u + z) + lqgQ γ * Real.log r)
      (m.map fun x => (x - z) / (r : ℂ)) := by
  set e := affineHomeomorph hr z
  have he : (fun x : ℂ => (x - z) / (r : ℂ)) = e := (coe_affineHomeomorph hr z).symm
  refine ⟨?_, ?_⟩
  · rw [he]
    have : IsFiniteMeasureOnCompacts (m.map e) := Measure.IsFiniteMeasureOnCompacts.map m e
    infer_instance
  · intro f hf hfc
    have hk : ∀ k : ℕ, ∫ x, f x ∂(lqgApprox γ (fun ε u => h (r * ε) ((r : ℂ) * u + z) +
        lqgQ γ * Real.log r) (dyadicScale k)) = ∫ x, f (e x) ∂(lqgApprox γ h (r * dyadicScale k)) := by
      intro k
      rw [lqgApprox_dilate_translate hγ h hr (by unfold dyadicScale; positivity) z, he,
        e.measurableEmbedding.integral_map]
    simp_rw [hk]
    rw [he, e.measurableEmbedding.integral_map]
    exact hm (fun x => f (e x)) (hf.comp e.continuous) (hfc.comp_homeomorph e)

/-- **Coordinate change rule for a fixed dilation and translation.** Let `μ` be the LQG measure of a whole-plane GFF
`h^ℂ`, `r > 0` and `z ∈ ℂ`. If almost surely the approximations of `h^ℂ` along the scales `r 2^{-k}` converge vaguely
to `μ`, then `μ((· - z) / r)⁻¹` is a positive finite random multiple of the LQG measure of the whole-plane GFF
`h^ℂ(r · + z) - h^ℂ_r(z)`. -/
theorem exists_coordChange_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hid : ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => ∫ x, f x ∂(lqgApprox γ (hcirc ω) (r * dyadicScale k))) atTop
        (𝓝 (∫ x, f x ∂(μ ω)))) :
    ∃ (hC'' : Ω → (ℂ → ℝ) → ℝ) (hcirc'' : Ω → ℝ → ℂ → ℝ) (μ'' : Ω → Measure ℂ) (c : Ω → ℝ≥0∞),
      IsWholePlaneGFF P hC'' hcirc'' ∧ IsLQGMeasure P γ hcirc'' μ'' ∧
      ∀ᵐ ω ∂P, c ω ≠ 0 ∧ c ω ≠ ∞ ∧ (μ ω).map (fun x => (x - z) / (r : ℂ)) = c ω • μ'' ω := by
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hG' := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG (r : ℂ)
    (Complex.ofReal_ne_zero.2 hr.ne') z
  rw [hnr] at hG'
  set d : Ω → ℝ := fun ω => hcirc ω r z + lqgQ γ * Real.log r with hd
  refine ⟨_, _, fun ω => ENNReal.ofReal (Real.exp (γ * -d ω)) • (μ ω).map (fun x => (x - z) / (r : ℂ)),
    fun ω => ENNReal.ofReal (Real.exp (γ * d ω)), hG', ?_, ?_⟩
  · filter_upwards [hμ, hid] with ω hω hidω
    have := hω.isLocallyFiniteMeasure
    have h1 := LQGMeasureNonatomicMass.isLQGLimit_add_const
      (isLQGLimit_dilate_translate hγ.ne' hr z hidω) (-d ω)
    have heq : (fun ε u => hcirc ω (r * ε) ((r : ℂ) * u + z) + lqgQ γ * Real.log r + -d ω) =
        fun ε u => hcirc ω (r * ε) ((r : ℂ) * u + z) - hcirc ω r z := by
      funext ε u; simp only [hd]; ring
    rw [heq] at h1
    exact h1
  · filter_upwards with ω
    refine ⟨by simp [Real.exp_pos], ENNReal.ofReal_ne_top, ?_⟩
    rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_neg, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one, one_smul]

end LQGCoordChangeFixed

end LatticeProb.LQG
