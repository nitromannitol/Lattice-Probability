import Mathlib
import LatticeProb.LQG.GMCDilation
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Affine covariance of the circle-average approximations of Gaussian multiplicative chaos

For circle averages `h : ℝ → ℂ → ℝ` (`h r z` is the average of the field over the circle of radius `r` about `z`),
`a ≠ 0` and `b`, the circle averages of the field `x ↦ h (a x + b) + Q log |a|` at scale `ε` and the point `z` are
`h (|a| ε) (a z + b) + Q log |a|`. Since `γ Q = 2 + γ²/2`, the Lebesgue-density approximation of this field at scale `ε`
is exactly the image, under `x ↦ (x - b) / a`, of the approximation of `h` at scale `|a| ε`. Consequently the vague
limit of the approximations of the shifted field along the dyadic scales `2^{-k}` is the image of the vague limit of the
approximations of `h` along the scales `|a| 2^{-k}`.

## Main results

* `lqgApprox_affine`: `lqgApprox γ (affineField γ a b h) ε = (lqgApprox γ h (‖a‖ ε)).map (fun x => (x - b) / a)`.
* `IsLQGLimitAlong`: vague convergence of the approximations along an arbitrary scale sequence;
  `isLQGLimit_iff_isLQGLimitAlong_dyadic` identifies it with `IsLQGLimit` along `dyadicScale`.
* `isLQGLimit_affine_map_of_along`: transfer of the limit along `‖a‖ 2^{-k}` to the shifted field.
* `isLQGLimitAlong_ratio_of_tendsto`, `isLQGLimitAlong_of_ratio_Ioc`: reduction to ratios in `(1/2, 1]`.
* `coordChangeLP_of_ratio_limit`: the literature input `LQGMeasureCoordChangeLP` follows from the almost sure
  convergence of the approximations along `r 2^{-k}`, for all `r ∈ (1/2, 1]` simultaneously, to the dyadic limit.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- Change of variables for the Lebesgue integral under the affine map `z ↦ a z + b` of the plane. -/
theorem lintegral_affine (g : ℂ → ℝ≥0∞) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ∫⁻ x, g x = ENNReal.ofReal (Complex.normSq a) * ∫⁻ z, g (a * z + b) := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ a) = Complex.normSq a := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hne : LinearMap.det (LinearMap.mulLeft ℝ a) ≠ 0 := by
    rw [hdet]; exact (Complex.normSq_pos.2 ha).ne'
  have hmap : Measure.map (fun z : ℂ => a * z) (volume : Measure ℂ) =
      ENNReal.ofReal (Complex.normSq a)⁻¹ • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
    have hfun : (⇑(LinearMap.mulLeft ℝ a) : ℂ → ℂ) = fun z => a * z := by
      ext z; simp
    rw [hfun, hdet, abs_of_pos (inv_pos.2 (Complex.normSq_pos.2 ha))] at this
    exact this
  have he : MeasurableEmbedding fun z : ℂ => a * z :=
    (Homeomorph.mulLeft₀ a ha).measurableEmbedding
  have h1 : ∫⁻ z, g (a * z + b) = ∫⁻ z, g (z + b) ∂(Measure.map (fun z : ℂ => a * z) volume) := by
    rw [he.lintegral_map]
  have h2 : ∫⁻ z, g (z + b) ∂(Measure.map (fun z : ℂ => a * z) volume) =
      ENNReal.ofReal (Complex.normSq a)⁻¹ * ∫⁻ x, g x := by
    rw [hmap, lintegral_smul_measure, lintegral_add_right_eq_self (fun x => g x) b, smul_eq_mul]
  rw [h1, h2, ← mul_assoc, ← ENNReal.ofReal_mul (Complex.normSq_pos.2 ha).le,
    mul_inv_cancel₀ (Complex.normSq_pos.2 ha).ne', ENNReal.ofReal_one, one_mul]

/-- The circle averages of the field `x ↦ h (a x + b) + Q log |a|`: `(ε, z) ↦ h (|a| ε) (a z + b) + Q log |a|`. -/
noncomputable def affineField (γ : ℝ) (a b : ℂ) (h : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ε z => h (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖

/-- The change of coordinates `x ↦ (x - b) / a`. -/
noncomputable def affineChart (a b : ℂ) : ℂ → ℂ := fun x => (x - b) / a

theorem measurable_affineChart (a b : ℂ) : Measurable (affineChart a b) := by
  unfold affineChart; fun_prop

theorem continuous_affineChart (a b : ℂ) : Continuous (affineChart a b) := by
  unfold affineChart; fun_prop

theorem affineChart_affine {a : ℂ} (ha : a ≠ 0) (b z : ℂ) : affineChart a b (a * z + b) = z := by
  unfold affineChart
  field_simp
  ring

/-- **Affine covariance of the approximation.** For `γ ≠ 0`, `a ≠ 0`, `b` and `ε ≥ 0`, the approximation of the field
`x ↦ h (a x + b) + Q log |a|` at scale `ε` is the image under `x ↦ (x - b) / a` of the approximation of `h` at
scale `|a| ε`. -/
theorem lqgApprox_affine {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    lqgApprox γ (affineField γ a b h) ε = (lqgApprox γ h (‖a‖ * ε)).map (affineChart a b) := by
  have hn : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hns : Complex.normSq a = ‖a‖ ^ 2 := Complex.normSq_eq_norm_sq a
  have hQ : Real.exp (γ * (lqgQ γ * Real.log ‖a‖)) = ‖a‖ ^ 2 * ‖a‖ ^ (γ ^ 2 / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hn, ← mul_lqgQ hγ, Real.rpow_def_of_pos hn]
    congr 1
    ring
  ext S hS
  rw [Measure.map_apply (measurable_affineChart a b) hS]
  simp only [lqgApprox]
  rw [withDensity_apply _ hS, withDensity_apply _ ((measurable_affineChart a b) hS),
    ← lintegral_indicator hS, ← lintegral_indicator ((measurable_affineChart a b) hS)]
  rw [lintegral_affine (fun x => (affineChart a b ⁻¹' S).indicator
      (fun x => ENNReal.ofReal ((‖a‖ * ε) ^ (γ ^ 2 / 2) * Real.exp (γ * h (‖a‖ * ε) x))) x) ha b,
    hns, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ S
  · have hz' : a * z + b ∈ affineChart a b ⁻¹' S := by
      show affineChart a b (a * z + b) ∈ S
      rw [affineChart_affine ha]; exact hz
    rw [indicator_of_mem hz, indicator_of_mem hz', ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [affineField]
    rw [Real.mul_rpow hn.le hε, mul_add, Real.exp_add, hQ]
    ring
  · have hz' : a * z + b ∉ affineChart a b ⁻¹' S := by
      show affineChart a b (a * z + b) ∉ S
      rw [affineChart_affine ha]; exact hz
    rw [indicator_of_notMem hz, indicator_of_notMem hz', mul_zero]

/-- The change of coordinates `x ↦ (x - b) / a` as a homeomorphism of the plane. -/
noncomputable def affineHomeo {a : ℂ} (ha : a ≠ 0) (b : ℂ) : ℂ ≃ₜ ℂ where
  toFun := affineChart a b
  invFun := fun z => a * z + b
  left_inv x := by
    unfold affineChart
    field_simp
    ring
  right_inv z := affineChart_affine ha b z
  continuous_toFun := continuous_affineChart a b
  continuous_invFun := by fun_prop

/-- `IsLQGLimitAlong γ h s m`: the measure `m` on `ℂ` is locally finite and is the vague limit of the approximations
`lqgApprox γ h (s k)` as `k → ∞`, for an arbitrary scale sequence `s`. For `s = dyadicScale` this is `IsLQGLimit`. -/
structure IsLQGLimitAlong (γ : ℝ) (h : ℝ → ℂ → ℝ) (s : ℕ → ℝ) (m : Measure ℂ) : Prop where
  /-- The limit is a Radon measure. -/
  isLocallyFiniteMeasure : IsLocallyFiniteMeasure m
  /-- Vague convergence along the scales `s k`. -/
  tendsto_integral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ h (s k))) atTop (𝓝 (∫ z, f z ∂m))

theorem isLQGLimit_iff_isLQGLimitAlong_dyadic {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ} :
    IsLQGLimit γ h m ↔ IsLQGLimitAlong γ h dyadicScale m :=
  ⟨fun H => ⟨H.isLocallyFiniteMeasure, H.tendsto_integral⟩,
    fun H => ⟨H.isLocallyFiniteMeasure, H.tendsto_integral⟩⟩

/-- **Transfer of the limit under an affine change of coordinates.** If the approximations of `h` converge vaguely to
`μ` along the scales `‖a‖ 2^{-k}`, then the dyadic approximations of the field `x ↦ h (a x + b) + Q log |a|` converge
vaguely to the image of `μ` under `x ↦ (x - b) / a`. -/
theorem isLQGLimit_affine_map_of_along {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {μ : Measure ℂ} (hμ : IsLQGLimitAlong γ h (fun k => ‖a‖ * dyadicScale k) μ) :
    IsLQGLimit γ (affineField γ a b h) (μ.map (affineChart a b)) := by
  have hdy : ∀ k, 0 ≤ dyadicScale k := fun k => pow_nonneg (by norm_num) k
  have hmeas : Measurable (affineChart a b) := measurable_affineChart a b
  refine ⟨?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨t, ht, htfin⟩ := hμ.isLocallyFiniteMeasure.finiteAtNhds ((affineHomeo ha b).symm x)
    refine ⟨(affineHomeo ha b).symm ⁻¹' t,
      (affineHomeo ha b).symm.continuous.continuousAt (by simpa using ht), ?_⟩
    have hpre : affineChart a b ⁻¹' ((affineHomeo ha b).symm ⁻¹' t) = t := by
      ext y
      change (affineHomeo ha b).symm (affineHomeo ha b y) ∈ t ↔ y ∈ t
      rw [Homeomorph.symm_apply_apply]
    change (Measure.map (affineHomeo ha b) μ) _ < ∞
    rw [(affineHomeo ha b).measurableEmbedding.map_apply]
    rw [show (affineHomeo ha b) ⁻¹' ((affineHomeo ha b).symm ⁻¹' t) = t from hpre]
    exact htfin
  · intro f hf hfc
    have hfψ : Continuous (f ∘ affineChart a b) := hf.comp (continuous_affineChart a b)
    have hfψc : HasCompactSupport (f ∘ affineChart a b) :=
      hfc.comp_homeomorph (affineHomeo ha b)
    have h1 := hμ.tendsto_integral _ hfψ hfψc
    have h2 : ∫ z, f z ∂(μ.map (affineChart a b)) = ∫ z, f (affineChart a b z) ∂μ :=
      integral_map hmeas.aemeasurable hf.aestronglyMeasurable
    rw [h2]
    refine h1.congr fun k => ?_
    rw [lqgApprox_affine hγ h ha b (hdy k), integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    rfl

/-- Vague convergence along a scale sequence tending to `0` from the right, from vague convergence of the whole
family of approximations as the scale tends to `0`. -/
theorem isLQGLimitAlong_of_tendsto_continuum {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : IsLocallyFiniteMeasure m)
    (H : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ h ε)) (𝓝[>] 0) (𝓝 (∫ z, f z ∂m)))
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝[>] 0)) : IsLQGLimitAlong γ h s m :=
  ⟨hm, fun f hf hfc => (H f hf hfc).comp hs⟩

/-- Shifting the index of the scale sequence does not change the limit. -/
theorem isLQGLimitAlong_shift_iff {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ} (s : ℕ → ℝ) (j : ℕ) :
    IsLQGLimitAlong γ h (fun k => s (k + j)) m ↔ IsLQGLimitAlong γ h s m := by
  refine ⟨fun H => ⟨H.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩,
    fun H => ⟨H.isLocallyFiniteMeasure, fun f hf hfc => ?_⟩⟩
  · exact (tendsto_add_atTop_iff_nat (f := fun k => ∫ z, f z ∂(lqgApprox γ h (s k))) j).1
      (H.tendsto_integral f hf hfc)
  · exact (tendsto_add_atTop_iff_nat (f := fun k => ∫ z, f z ∂(lqgApprox γ h (s k))) j).2
      (H.tendsto_integral f hf hfc)

/-- **Reduction to ratios in `(1/2, 1]`.** If the approximations converge vaguely to `m` along `r 2^{-k}` for every
`r ∈ (1/2, 1]`, they do so along `c 2^{-k}` for every `c > 0`. -/
theorem isLQGLimitAlong_of_ratio_Ioc {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (H : ∀ r ∈ Ioc (1 / 2 : ℝ) 1, IsLQGLimitAlong γ h (fun k => r * dyadicScale k) m) {c : ℝ}
    (hc : 0 < c) : IsLQGLimitAlong γ h (fun k => c * dyadicScale k) m := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hc (one_lt_two : (1 : ℝ) < 2)
  have h2n : (0 : ℝ) < 2 ^ (n + 1) := zpow_pos (by norm_num) _
  have hsplit : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by
    rw [zpow_add_one₀ (by norm_num), mul_comm]
  have h2n' : (0 : ℝ) < 2 ^ n := zpow_pos (by norm_num) _
  set r : ℝ := c / 2 ^ (n + 1) with hr
  have hrc : c = r * 2 ^ (n + 1) := by rw [hr]; field_simp
  have hrmem : r ∈ Ioc (1 / 2 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · rw [hr, lt_div_iff₀ h2n, hsplit]; linarith
    · rw [hr, div_le_one h2n]; exact hn2
  have hH := H r hrmem
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg (n + 1)
  · rw [hm, zpow_natCast] at hrc
    have heq : ∀ k, c * dyadicScale (k + m) = r * dyadicScale k := by
      intro k
      rw [hrc]
      unfold dyadicScale
      rw [pow_add, show r * 2 ^ m * ((2 : ℝ)⁻¹ ^ k * (2 : ℝ)⁻¹ ^ m) =
        r * (2 : ℝ)⁻¹ ^ k * (2 ^ m * (2 : ℝ)⁻¹ ^ m) by ring, ← mul_pow,
        mul_inv_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_pow, mul_one]
    rw [← isLQGLimitAlong_shift_iff (fun k => c * dyadicScale k) m]
    simpa only [heq] using hH
  · rw [hm, zpow_neg, zpow_natCast] at hrc
    have heq : ∀ k, c * dyadicScale k = r * dyadicScale (k + m) := by
      intro k
      rw [hrc]
      unfold dyadicScale
      rw [pow_add]
      simp only [inv_pow]
      ring
    have := (isLQGLimitAlong_shift_iff (fun k => r * dyadicScale k) m).2 hH
    simpa only [heq] using this

theorem tendsto_ratio_dyadicScale (r : ℝ) (hr : 0 < r) :
    Tendsto (fun k : ℕ => r * dyadicScale k) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
  · have h0 : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := h0.const_mul r
    rw [mul_zero] at this
    exact this
  · exact mul_pos hr (pow_pos (by norm_num) k)

/-- **Reduction of the coordinate change to ratios.** The literature input `LQGMeasureCoordChangeLP` (a.s., for all
complex affine maps simultaneously, the dyadic approximations of the shifted field converge to the image of the LQG
measure) follows from the following: almost surely, for every ratio `r ∈ (1/2, 1]`, the approximations of the field
converge vaguely to the LQG measure along the scales `r 2^{-k}`. -/
theorem coordChangeLP_of_ratio_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (H : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1,
        IsLQGLimitAlong γ (fieldCircleAverage α₀ (hcirc ω)) (fun k => r * dyadicScale k) (μ ω)) :
    LQGMeasureCoordChangeLP P γ α₀ hC hcirc := by
  intro hG hγ0 hγ2 hα μ hμ
  filter_upwards [H hG hγ0 hγ2 hα μ hμ] with ω hω a ha b
  exact isLQGLimit_affine_map_of_along hγ0.ne' _ ha b
    (isLQGLimitAlong_of_ratio_Ioc hω (norm_pos_iff.2 ha))

/-- **Reduction of the coordinate change to the continuum limit.** `LQGMeasureCoordChangeLP` follows from the almost
sure vague convergence of the whole family of approximations `lqgApprox γ h ε` to the LQG measure as `ε → 0+`
(not only along dyadic scales). -/
theorem coordChangeLP_of_continuum_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (H : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
        Tendsto (fun ε : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) ε)) (𝓝[>] 0)
          (𝓝 (∫ z, f z ∂(μ ω)))) :
    LQGMeasureCoordChangeLP P γ α₀ hC hcirc := by
  refine coordChangeLP_of_ratio_limit P γ α₀ hC hcirc fun hG hγ0 hγ2 hα μ hμ => ?_
  filter_upwards [H hG hγ0 hγ2 hα μ hμ, hμ] with ω hω hωlim r hr
  exact isLQGLimitAlong_of_tendsto_continuum hωlim.isLocallyFiniteMeasure hω
    (tendsto_ratio_dyadicScale r (by linarith [hr.1]))

end LatticeProb.LQG
