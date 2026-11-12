import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.LQG.LQGMeasureNonatomicOrigin

/-! # Existence of the LQG measure for a nonpositive logarithmic singularity

For the whole-plane GFF `h^ℂ` and `h = h^ℂ - α log |·|`, the circle-average approximations satisfy
`e^{γ h_ε(z)} = e^{γ h'_ε(z)} max(ε, |z|)^{γ(β-α)}` for `h' = h^ℂ - β log |·|`, since the circle average of `log |·|`
on `∂B_ε(z)` is `log max(ε, |z|)` (Jensen's formula). For `α ≤ β` the weight is a nonnegative power, and it converges
to `|z|^{γ(β-α)}` uniformly on compact sets as `ε → 0`. Hence a vague limit `ν` for the stronger singularity `β` gives
the vague limit `|z|^{γ(β-α)} ν(dz)` for the weaker singularity `α` (Duplantier-Sheffield 2011, Section 2; this is the
usual Weyl-type reweighting by a continuous function).

Main results:
* `isLQGLimit_fieldCircleAverage_of_le`: the deterministic reweighting of an `IsLQGLimit`.
* `lqgMeasureExistenceLP_of_le`: existence at `β < Q` gives existence at every `α ≤ β`.
* `lqgMeasureExistenceLP_zero`: existence without insertion, from the almost sure dyadic limit
  (`LatticeProb.Gauss.IsWholePlaneGFF.exists_isLQGMeasure`).
* `lqgMeasureExistenceLP_of_nonpos`: `LQGMeasureExistenceLP P γ α₀ hC hcirc` for every `α₀ ≤ 0`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

namespace LQGMeasureExistenceNonpos

open LatticeProb.LQG.ProfileDerived (dyadicScale_pos isLocallyFiniteMeasure_lqgApprox)
open LatticeProb.LQG.LQGWeylScalingDerived (tendsto_integral_of_uniformOn_compact
  ae_continuous_fieldCircleAverage_of_isWholePlaneGFF)
open LatticeProb.LQG.LQGMeasureNonatomicOrigin (fieldCircleAverage_eq_log)

/-- The approximation for the singularity `α` is the approximation for `β` reweighted by `max(r, |z|)^{γ(β-α)}`. -/
theorem lqgApprox_fieldCircleAverage_eq_withDensity {γ α β r : ℝ} (hr : 0 < r)
    (hp : 0 ≤ γ * (β - α)) (hcirc : ℝ → ℂ → ℝ)
    (hc : Continuous (fieldCircleAverage β hcirc r)) :
    lqgApprox γ (fieldCircleAverage α hcirc) r =
      (lqgApprox γ (fieldCircleAverage β hcirc) r).withDensity
        (fun z => ENNReal.ofReal (max r ‖z‖ ^ (γ * (β - α)))) := by
  have ha : Measurable (fun z => ENNReal.ofReal
      (r ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage β hcirc r z))) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hc))).measurable
  have hw : Continuous (fun z : ℂ => max r ‖z‖ ^ (γ * (β - α))) :=
    (Real.continuous_rpow_const hp).comp (continuous_const.max continuous_norm)
  have hb : Measurable (fun z => ENNReal.ofReal (max r ‖z‖ ^ (γ * (β - α)))) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  simp only [lqgApprox]
  rw [← withDensity_mul volume ha hb]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _))]
  congr 1
  rw [Real.rpow_def_of_pos (lt_max_of_lt_left hr)]
  have he : γ * fieldCircleAverage α hcirc r z =
      γ * fieldCircleAverage β hcirc r z + Real.log (max r ‖z‖) * (γ * (β - α)) := by
    rw [fieldCircleAverage_eq_log α hcirc hr, fieldCircleAverage_eq_log β hcirc hr]
    ring
  rw [he, Real.exp_add]
  ring

/-- Integration against a continuous nonnegative density. -/
theorem integral_withDensity_ofReal_eq_integral_mul (μ : Measure ℂ) (w φ : ℂ → ℝ)
    (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) :
    (∫ z, φ z ∂(μ.withDensity fun z => ENNReal.ofReal (w z))) = ∫ z, φ z * w z ∂μ := by
  have hm : Measurable (fun z => ENNReal.ofReal (w z)) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm (by filter_upwards [] with z; simp) φ]
  congr 1
  funext z
  simp [hw0 z, mul_comm]

/-- `φ(z) max(2^{-n}, |z|)^p → φ(z) |z|^p` uniformly on compact sets, for `p ≥ 0` and continuous `φ`. -/
theorem tendstoUniformlyOn_mul_max_dyadicScale_rpow (p : ℝ) (hp : 0 ≤ p)
    (φ : ℂ → ℝ) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => φ z * max (dyadicScale n) ‖z‖ ^ p)
      (fun z => φ z * ‖z‖ ^ p) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun q : ℝ × ℂ => φ q.2 * max q.1 ‖q.2‖ ^ p) :=
    (hφ.comp continuous_snd).mul ((Real.continuous_rpow_const hp).comp
      (continuous_fst.max (continuous_norm.comp continuous_snd)))
  have hu : UniformContinuousOn
      (fun q : ℝ × ℂ => φ q.2 * max q.1 ‖q.2‖ ^ p) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * max r ‖z‖ ^ p) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * max r ‖z‖ ^ p)
      (fun z => φ z * ‖z‖ ^ p) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, max_eq_right (norm_nonneg _)] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  have hscale : Tendsto dyadicScale atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact hscale.eventually (ht' ε hε)

/-- A vague limit `ν` for the singularity `β` gives the vague limit `|z|^{γ(β-α)} ν(dz)` for every weaker
singularity `α ≤ β`. -/
theorem isLQGLimit_fieldCircleAverage_of_le {γ α β : ℝ} (hγ : 0 ≤ γ) (hαβ : α ≤ β)
    (hcirc : ℝ → ℂ → ℝ) {ν : Measure ℂ}
    (hν : IsLQGLimit γ (fieldCircleAverage β hcirc) ν)
    (hc : ∀ n, Continuous (fieldCircleAverage β hcirc (dyadicScale n))) :
    IsLQGLimit γ (fieldCircleAverage α hcirc)
      (ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
  let p := γ * (β - α)
  have hp : 0 ≤ p := mul_nonneg hγ (sub_nonneg.mpr hαβ)
  let : IsLocallyFiniteMeasure ν := hν.isLocallyFiniteMeasure
  let νn : ℕ → Measure ℂ := fun n => lqgApprox γ (fieldCircleAverage β hcirc) (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (νn n) := fun n => isLocallyFiniteMeasure_lqgApprox γ (hc n)
  have hw : Continuous (fun z : ℂ => ‖z‖ ^ p) :=
    (Real.continuous_rpow_const hp).comp continuous_norm
  constructor
  · exact IsLocallyFiniteMeasure.withDensity_ofReal hw
  · intro φ hφ hφc
    let K := tsupport φ
    have hK : IsCompact K := hφc
    let g : ℕ → ℂ → ℝ := fun n z => φ z * max (dyadicScale n) ‖z‖ ^ p
    let g₀ : ℂ → ℝ := fun z => φ z * ‖z‖ ^ p
    have hg : ∀ n, Integrable (g n) (νn n) := by
      intro n
      have hgc : Continuous (g n) := hφ.mul ((Real.continuous_rpow_const hp).comp
        (continuous_const.max continuous_norm))
      exact hgc.integrable_of_hasCompactSupport hφc.mul_right
    have huni : TendstoUniformlyOn g g₀ atTop K :=
      tendstoUniformlyOn_mul_max_dyadicScale_rpow p hp φ hφ hK
    have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
      intro n z hz
      have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [g, g₀, hz']
    have hlim := tendsto_integral_of_uniformOn_compact νn ν hν.tendsto_integral hK
      (hφ.mul hw) hφc.mul_right hg huni hoff
    have heq (n : ℕ) : (∫ z, φ z ∂(lqgApprox γ (fieldCircleAverage α hcirc) (dyadicScale n))) =
        ∫ z, g n z ∂(νn n) := by
      rw [lqgApprox_fieldCircleAverage_eq_withDensity (dyadicScale_pos n) hp hcirc (hc n)]
      exact integral_withDensity_ofReal_eq_integral_mul (νn n) _ φ
        ((Real.continuous_rpow_const hp).comp (continuous_const.max continuous_norm))
        (fun z => Real.rpow_nonneg (le_max_of_le_right (norm_nonneg z)) p)
    simp_rw [heq]
    change Tendsto (fun n => ∫ z, g n z ∂(νn n)) atTop
      (𝓝 (∫ z, φ z ∂(ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ p))))
    rw [integral_withDensity_ofReal_eq_integral_mul ν _ φ hw
      (fun z => Real.rpow_nonneg (norm_nonneg z) p)]
    exact hlim

/-- Existence of the LQG measure at a singularity `β < Q` gives existence at every weaker singularity `α ≤ β`, by
the reweighting `|z|^{γ(β-α)}`. -/
theorem lqgMeasureExistenceLP_of_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α β : ℝ}
    (hαβ : α ≤ β) (hβ : β < lqgQ γ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistenceLP P γ β hC hcirc) :
    LQGMeasureExistenceLP P γ α hC hcirc := by
  intro hG hγ hγ2 _
  obtain ⟨ν, hν⟩ := hE hG hγ hγ2 hβ
  refine ⟨fun ω => (ν ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))), ?_⟩
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage β (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => ae_continuous_fieldCircleAverage_of_isWholePlaneGFF hG β (dyadicScale_pos n))
  filter_upwards [hν, hc] with ω hνω hcω
  exact isLQGLimit_fieldCircleAverage_of_le hγ.le hαβ (hcirc ω) hνω hcω

/-- Existence of the LQG measure of the whole-plane GFF without insertion (`α₀ = 0`), for `0 < γ < 2`. -/
theorem lqgMeasureExistenceLP_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureExistenceLP P γ 0 hC hcirc := by
  intro hG hγ hγ2 _
  obtain ⟨μ, hμ⟩ := hG.exists_isLQGMeasure hγ hγ2
  refine ⟨μ, ?_⟩
  have hf : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  unfold IsLQGMeasureOfField
  rw [hf]
  exact hμ

/-- `0 < Q = 2/γ + γ/2` for `γ > 0`. -/
theorem lqgQ_pos {γ : ℝ} (hγ : 0 < γ) : 0 < lqgQ γ := by
  unfold lqgQ
  positivity

/-- Existence of the LQG measure of `h^ℂ - α₀ log |·|` for every `α₀ ≤ 0` and `0 < γ < 2`. -/
theorem lqgMeasureExistenceLP_of_nonpos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ : ℝ}
    (hα₀ : α₀ ≤ 0) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureExistenceLP P γ α₀ hC hcirc := by
  intro hG hγ hγ2 hαQ
  exact lqgMeasureExistenceLP_of_le P hα₀ (lqgQ_pos hγ) hC hcirc
    (lqgMeasureExistenceLP_zero P γ hC hcirc) hG hγ hγ2 hαQ

end LQGMeasureExistenceNonpos

end LatticeProb.LQG
