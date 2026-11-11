import Mathlib
import LatticeProb.LQG.LQGWeylScaling
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Non-atomicity at the logarithmic singularity (chain)

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Fact 2.1 I: the origin part of the non-atomicity argument, together with its comparison lemma for vague limits. The
statements use the names `IsWholePlaneGFF`, `IsLQGLimit`, `IsLQGMeasureOfField`, `lqgApprox`, `fieldCircleAverage`,
`addCircleAverage`, `dyadicScale`, `lqgQ` and `LQGMeasureExistenceLP` (module `LatticeProb.LQG.LQGMeasureInputs`).

Content: a locally finite vague limit with a stronger logarithmic singularity has no atom at `0`, so an LQG measure of
strength `α` has no atom at `0` when existence holds at a strictly larger strength `β ∈ (α, Q)` (Duplantier-Sheffield 2011,
Prop. 1.1 for the vague limits; Armitage-Gardiner for the compact-set comparison of measures). The argument uses only
circle averages, the Gaussian-free-field continuity of the circle averages (`ae_continuous_fieldCircleAverage_of_isWholePlaneGFF`),
and the existence hypothesis `LQGMeasureExistenceLP` at the strength `β`. No hypothesis about the atom at `0` is assumed.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos isLocallyFiniteMeasure_lqgApprox circleAverage_log_norm_eq)
open LatticeProb.LQG.LQGWeylScalingDerived (isLQGLimit_addCircleAverage ae_continuous_fieldCircleAverage_of_isWholePlaneGFF)

namespace LatticeProb.LQG.LQGMeasureNonatomicOrigin

/-- Local inequalities on nonnegative continuous test functions imply the same inequality for compact sets. -/
theorem measure_compact_le_of_integral_le_of_tsupport_subset
    {U : Set ℂ} (hU : IsOpen U) {ν ν' : Measure ℂ}
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ν']
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x, 0 ≤ f x) → ∫ x, f x ∂ν ≤ ∫ x, f x ∂ν')
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) : ν K ≤ ν' K := by
  rw [hK.measure_eq_iInf_isOpen (μ := ν')]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  obtain ⟨f, hf1, hfc, hfV, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter hU) (subset_inter hKV hKU)
  have hfint : ∀ μ : Measure ℂ, [IsLocallyFiniteMeasure μ] → Integrable (f : ℂ → ℝ) μ :=
    fun μ _ => f.continuous.integrable_of_hasCompactSupport hfc
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have h1 : ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν) (Eventually.of_forall hnn)]
    calc ν K = ∫⁻ x, K.indicator 1 x ∂ν := by rw [lintegral_indicator_one hK.measurableSet]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [hx, hf1 hx]
        · simp [hx]
  have h2 : ENNReal.ofReal (∫ x, f x ∂ν') ≤ ν' (V ∩ U) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν') (Eventually.of_forall hnn)]
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν' ≤ ∫⁻ x, (V ∩ U).indicator 1 x ∂ν' := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ V ∩ U
          · have := (hf01 x).2
            simp [hx, this]
          · have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfV hx'))
            simp [hx, this]
      _ = ν' (V ∩ U) := by rw [lintegral_indicator_one (hV.inter hU).measurableSet]
  calc ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := h1
    _ ≤ ENNReal.ofReal (∫ x, f x ∂ν') :=
      ENNReal.ofReal_le_ofReal (h f f.continuous hfc (hfV.trans inter_subset_right) hnn)
    _ ≤ ν' (V ∩ U) := h2
    _ ≤ ν' V := measure_mono inter_subset_left

/-- If the regularized fields are eventually ordered on each compact subset of an open set, their vague-limit
measures are ordered on compact subsets. -/
theorem isLQGLimit_measure_compact_le {γ : ℝ} (hγ : 0 ≤ γ)
    {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m')
    (hc' : ∀ k, Continuous (hε' (dyadicScale k)))
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hloc : ∀ L : Set ℂ, IsCompact L → L ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ L, hε (dyadicScale k) z ≤ hε' (dyadicScale k) z) :
    m K ≤ m' K := by
  let : IsLocallyFiniteMeasure m := hm.isLocallyFiniteMeasure
  let : IsLocallyFiniteMeasure m' := hm'.isLocallyFiniteMeasure
  apply measure_compact_le_of_integral_le_of_tsupport_subset hU _ hK hKU
  intro f hf hfc hfU hnn
  have hmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hzero : ∀ ν : Measure ℂ, ∫ x, f x ∂ν = ∫ x in tsupport f, f x ∂ν := fun ν =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport hx).symm
  have hle : ∀ᶠ k : ℕ in atTop,
      (∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) ≤
        ∫ z, f z ∂(lqgApprox γ hε' (dyadicScale k)) := by
    filter_upwards [hloc _ hfc hfU] with k hk
    let : IsLocallyFiniteMeasure (lqgApprox γ hε' (dyadicScale k)) :=
      isLocallyFiniteMeasure_lqgApprox γ (hc' k)
    have hmeasure : (lqgApprox γ hε (dyadicScale k)).restrict (tsupport f) ≤
        (lqgApprox γ hε' (dyadicScale k)).restrict (tsupport f) := by
      simp only [lqgApprox]
      rw [restrict_withDensity hmeas, restrict_withDensity hmeas]
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hmeas] with z hz
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hk z hz) hγ))
        (Real.rpow_nonneg (dyadicScale_pos k).le _)
    rw [hzero (lqgApprox γ hε (dyadicScale k)), hzero (lqgApprox γ hε' (dyadicScale k))]
    exact integral_mono_measure hmeasure (Eventually.of_forall hnn)
      ((hf.integrable_of_hasCompactSupport hfc).mono_measure Measure.restrict_le_self)
  exact le_of_tendsto_of_tendsto (hm.tendsto_integral f hf hfc) (hm'.tendsto_integral f hf hfc) hle

/-- The dyadic radii decrease to zero through positive values. -/
theorem tendsto_dyadicScale_nhdsGT : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact Eventually.of_forall dyadicScale_pos

/-- The field circle average in logarithmic form: `fieldCircleAverage α₀ hcirc r z = hcirc r z - α₀ log (max r ‖z‖)`. -/
theorem fieldCircleAverage_eq_log (α₀ : ℝ) (hcirc : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    fieldCircleAverage α₀ hcirc r z = hcirc r z - α₀ * Real.log (max r ‖z‖) := by
  have hmax : Real.log r + (r⁻¹ * ‖z‖).posLog = Real.log (max r ‖z‖) := by
    rw [Real.posLog, inv_mul_eq_div]
    rcases le_total r ‖z‖ with h | h
    · have hz : 0 < ‖z‖ := lt_of_lt_of_le hr h
      have hl : 0 ≤ Real.log (‖z‖ / r) := Real.log_nonneg ((one_le_div hr).2 h)
      rw [max_eq_right hl, max_eq_right h, Real.log_div hz.ne' hr.ne']
      ring
    · have hl : Real.log (‖z‖ / r) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hr).2 h)
      rw [max_eq_left hl, max_eq_left h]
      ring
  rw [fieldCircleAverage, circleAverage_log_norm_eq hr, hmax]

/-- A locally finite LQG limit with a stronger logarithmic singularity forces any weaker singularity, formed from the
same circle averages, to have no atom at zero. -/
theorem origin_nonatomic_of_stronger_singularity
    {γ α β : ℝ} (hγ : 0 < γ) (hαβ : α < β)
    (hcirc : ℝ → ℂ → ℝ) (μ ν : Measure ℂ)
    (hm : IsLQGLimit γ (fieldCircleAverage α hcirc) μ)
    (hn : IsLQGLimit γ (fieldCircleAverage β hcirc) ν)
    (hc : ∀ k, Continuous (fieldCircleAverage β hcirc (dyadicScale k))) :
    μ {0} = 0 := by
  let : IsLocallyFiniteMeasure μ := hm.isLocallyFiniteMeasure
  let : IsLocallyFiniteMeasure ν := hn.isLocallyFiniteMeasure
  have hmfin : μ {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  have hnfin : ν {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  have hbound (n : ℕ) : (μ {0}).toReal ≤ Real.exp (-γ * n) * (ν {0}).toReal := by
    let R : ℝ := Real.exp (-((n : ℝ) + 1) / (β - α))
    have hR : 0 < R := Real.exp_pos _
    have hlogR : Real.log R = -((n : ℝ) + 1) / (β - α) := Real.log_exp _
    let f : ℂ → ℝ := fun _ => -(n : ℝ)
    have hf : Continuous f := continuous_const
    have hw := isLQGLimit_addCircleAverage hn hc f hf
    have hc' : ∀ k, Continuous (addCircleAverage (fieldCircleAverage β hcirc) f (dyadicScale k)) := by
      intro k
      change Continuous (fun z => fieldCircleAverage β hcirc (dyadicScale k) z +
        Real.circleAverage (fun _ : ℂ => -(n : ℝ)) z (dyadicScale k))
      simp only [Real.circleAverage_const]
      exact (hc k).add continuous_const
    have hloc : ∀ L : Set ℂ, IsCompact L → L ⊆ ball (0 : ℂ) R →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ L,
          fieldCircleAverage α hcirc (dyadicScale k) z ≤
            addCircleAverage (fieldCircleAverage β hcirc) f (dyadicScale k) z := by
      intro L _ hL
      filter_upwards [(tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds hR)] with k hk z hz
      have hr := dyadicScale_pos k
      have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hL hz
      have hmax : 0 < max (dyadicScale k) ‖z‖ := lt_max_of_lt_left hr
      have hmaxR : max (dyadicScale k) ‖z‖ ≤ R := max_le hk.le hzR.le
      have hl : Real.log (max (dyadicScale k) ‖z‖) ≤ Real.log R := Real.log_le_log hmax hmaxR
      have hd : 0 < β - α := sub_pos.mpr hαβ
      have hp : (β - α) * Real.log (max (dyadicScale k) ‖z‖) ≤ -((n : ℝ) + 1) := by
        calc
          _ ≤ (β - α) * Real.log R := mul_le_mul_of_nonneg_left hl hd.le
          _ = -((n : ℝ) + 1) := by rw [hlogR]; field_simp
      rw [fieldCircleAverage_eq_log _ _ hr, addCircleAverage, Real.circleAverage_const,
        fieldCircleAverage_eq_log _ _ hr]
      nlinarith
    have hle := isLQGLimit_measure_compact_le hγ.le hm hw hc'
      (U := ball (0 : ℂ) R) (K := {0}) isOpen_ball isCompact_singleton
      (by simpa using hR) hloc
    change μ {0} ≤ (ν.withDensity (fun _ => ENNReal.ofReal (Real.exp (γ * -(n : ℝ))))) {0} at hle
    rw [withDensity_const, Measure.smul_apply] at hle
    have ht : ENNReal.ofReal (Real.exp (γ * -(n : ℝ))) * ν {0} ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) hnfin
    have hreal := ENNReal.toReal_mono ht hle
    simpa [f, ENNReal.toReal_mul, Real.exp_nonneg, mul_neg] using hreal
  have hlim : Tendsto (fun n : ℕ => Real.exp (-γ * n) * (ν {0}).toReal) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => -γ * (n : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hγ)
    simpa using (Real.tendsto_exp_atBot.comp ht).mul_const (ν {0}).toReal
  have hz : (μ {0}).toReal = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)) ENNReal.toReal_nonneg
  rw [ENNReal.toReal_eq_zero_iff] at hz
  exact hz.resolve_right hmfin

/-- Existence at any strictly larger subcritical singularity `β ∈ (α, Q)` removes the atom at zero of the LQG measure of
strength `α`. The existence input is
`LQGMeasureExistenceLP` at `β`, used only as a hypothesis. -/
theorem ae_origin_nonatomic_of_stronger_existence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαβ : α < β) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistenceLP P γ β hC hcirc)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) : ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  obtain ⟨ν, hν⟩ := hE hG hγ hγ2 hβ
  have hc : ∀ᵐ ω ∂P, ∀ k, Continuous (fieldCircleAverage β (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => ae_continuous_fieldCircleAverage_of_isWholePlaneGFF hG β (dyadicScale_pos k))
  filter_upwards [hμ, hν, hc] with ω hm hn hc
  exact origin_nonatomic_of_stronger_singularity hγ hαβ (hcirc ω) (μ ω) (ν ω) hm hn hc

end LatticeProb.LQG.LQGMeasureNonatomicOrigin
