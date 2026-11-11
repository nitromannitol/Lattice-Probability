import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.Gauss.CircleAverageApprox2

/-! # Affine invariance of the whole-plane GFF: LP form

LP form of the affine invariance of the whole-plane GFF (arXiv:2208.11795; Gwynne-Holden-Sun 2019, Section 3.2.2; Berestycki-Powell, Corollary 5.7 and Lemma 6.26): for
`a ∈ ℂ ∖ {0}` and `b ∈ ℂ`, the transformed pairings `φ ↦ |a|⁻² hC(φ ∘ F⁻¹) - hcirc |a| b · ∫ φ` and circle averages
`(r, z) ↦ hcirc (|a| r) (a z + b) - hcirc |a| b` (with `F z = a z + b`) again form a whole-plane GFF.

The statement is the same expression, stated for the definitions of this library (`IsWholePlaneGFF`, `GFFObservable`, `wholePlaneCov`, `wholePlaneGFFCov`, `IsTestFunction`). The proof is adapted from the derivation of the affine invariance in the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795], together with the closure of the auxiliary declarations it uses (the affine core, kernel and algebra lemmas, and the dilation-mixing, pairing-covariance, circle-density and Green-identity lemmas) and the `IsWholePlaneGFF` lemmas of that formalization. No new mathematics and no new input: the Gaussian, measurability,
centring, covariance and continuity clauses are checked from `IsWholePlaneGFF` alone, with the covariance identity
`cov_det_identity` and `cov(circle 1 0, ·) = 0` from `IsWholePlaneGFF.ae_circleAverage_one_zero`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open LatticeProb.Gauss

noncomputable section

namespace LatticeProb.Gauss

/-- In the closed unit disk the covariance kernel is `-log |z - w|`. -/
theorem wholePlaneCov_eq_neg_log {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    wholePlaneCov z w = -Real.log ‖z - w‖ := by
  rw [wholePlaneCov, max_eq_right hz, max_eq_right hw, one_mul, one_div, Real.log_inv]
/-- The kernel averaged over `y ∈ ∂B_1(0)` vanishes at every point `x` of the unit circle. -/
theorem circleAverage_wholePlaneCov_of_norm_eq_one {x : ℂ} (hx : ‖x‖ = 1) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 1 = 0 := by
  have h : Real.circleAverage (fun y => wholePlaneCov x y) 0 1 =
      Real.circleAverage (fun y => -Real.log ‖y - x‖) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro y hy
    have hy' : ‖y‖ = 1 := by simpa using hy
    simp only
    rw [wholePlaneCov_eq_neg_log hx.le hy'.le, norm_sub_rev]
  have h0 := circleAverage_log_norm_sub_const₁ hx
  rw [Real.circleAverage_def] at h0
  rw [h, Real.circleAverage_def, intervalIntegral.integral_neg, smul_neg, h0, neg_zero]
/-- The variance of the unit circle average `h^ℂ_1(0)` vanishes: the covariance kernel encodes the
normalization `h^ℂ_1(0) = 0`. -/
theorem wholePlaneGFFCov_circle_one_zero :
    wholePlaneGFFCov (.circle 1 0) (.circle 1 0) = 0 := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) 0 1) 0 1 = 0
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)), Real.circleAverage_const]
  intro x hx
  exact circleAverage_wholePlaneCov_of_norm_eq_one (by simpa using hx)
namespace IsWholePlaneGFF
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}
/-- The normalization `h^ℂ_1(0) = 0` holds a.s. -/
theorem ae_circleAverage_one_zero (hh : IsWholePlaneGFF P hC hcirc) : ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 := by
  have := hh.isProbabilityMeasure
  have hG := hh.hasGaussianLaw_circle one_pos 0
  have hL2 : MemLp (fun ω => hcirc ω 1 0) 2 P := hG.memLp (by simp)
  have hcov := hh.covariance_eq (.circle 1 0) (.circle 1 0) one_pos one_pos
  rw [wholePlaneGFFCov_circle_one_zero] at hcov
  have hvar : Var[fun ω => hcirc ω 1 0; P] = 0 := by
    rw [← covariance_self hG.aemeasurable]
    exact hcov
  have hmean : ∫ ω, hcirc ω 1 0 ∂P = 0 := hh.integral_eq_zero (.circle 1 0) one_pos
  filter_upwards [ae_eq_integral_of_variance_eq_zero hL2 hvar] with ω hω
  rw [hω, hmean]
end IsWholePlaneGFF

end LatticeProb.Gauss

namespace LatticeProb.LQG.AffineDerived

section Fundamental

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

theorem abs_log_le_inv_add_self {s : ℝ} (hs : 0 < s) : |Real.log s| ≤ s⁻¹ + s := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [Real.log_inv] at this
    linarith
  · have := Real.log_le_sub_one_of_pos hs
    linarith [inv_pos.2 hs]
/-- `log |·|` is integrable on every disc `B_r(0)` of the plane. -/
theorem integrableOn_ball_log_norm (r : ℝ) :
    IntegrableOn (fun y : ℂ => Real.log ‖y‖) (ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1 + r ^ 2) (α := 1) (by simp) (by simp) ?_
    (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
  refine ae_restrict_of_forall_mem measurableSet_ball fun y hy => ?_
  rw [mem_ball_zero_iff] at hy
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hs : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rw [Real.norm_eq_abs, Real.rpow_neg_one]
  refine (abs_log_le_inv_add_self hs).trans ?_
  have h1 : ‖y‖ ≤ r ^ 2 * ‖y‖⁻¹ := by
    rw [le_mul_inv_iff₀ hs]
    nlinarith
  nlinarith
/-- A function integrable on every disc `B_r(0)` and translated by `x` is locally integrable. -/
theorem locallyIntegrable_comp_sub_of_integrableOn_ball {f : ℂ → ℝ}
    (hf : ∀ r, IntegrableOn f (ball 0 r)) (x : ℂ) :
    LocallyIntegrable (fun y => f (y - x)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball x
  have h := (measurePreserving_sub_right volume x).integrableOn_comp_preimage
    (measurableEmbedding_subRight x) |>.2 (hf r)
  refine h.mono_set fun y hy => ?_
  simpa [mem_preimage, mem_ball, dist_eq_norm] using hr hy
theorem ae_ne_complex (x : ℂ) : ∀ᵐ y : ℂ, y ≠ x := by
  rw [ae_iff]
  simp
end Fundamental

section CircleLogPotential

open MeasureTheory Set Metric Filter
open scoped Topology Real

/-- The continuous normalization term in the whole-plane covariance kernel. -/
noncomputable def wholePlaneNormalization (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)
theorem continuous_wholePlaneNormalization : Continuous wholePlaneNormalization := by
  unfold wholePlaneNormalization
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
end CircleLogPotential

section S11uKernel

open MeasureTheory Filter Set Metric Topology

/-- `a x = log max(|x|, 1)`: the additive part of the whole-plane covariance kernel. -/
noncomputable def logMaxAbs (x : ℂ) : ℝ := Real.log (max ‖x‖ 1)
theorem logMaxAbs_continuous : Continuous logMaxAbs := by
  unfold logMaxAbs
  exact (continuous_norm.max continuous_const).log
    (fun x => ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _)))
/-- Off the diagonal the whole-plane kernel is `a x + a y - log |x - y|`. -/
theorem wholePlaneCov_eq_of_ne {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖ := by
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hy : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  unfold wholePlaneCov logMaxAbs
  rw [Real.log_div (mul_ne_zero hx hy) hd, Real.log_mul hx hy]
/-- Jensen's formula: the average of `log |y - w|` over `∂B_ρ(z)` is `log max(ρ, |z - w|)`. -/
theorem circleAverage_log_norm_sub_eq (z w : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => Real.log ‖y - w‖) z ρ = Real.log (max ρ ‖z - w‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hρ.ne',
    Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hρ.ne'
      (ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _))),
    mul_max_of_nonneg _ _ hρ.le, mul_one, mul_inv_cancel_left₀ hρ.ne']
/-- The circle average of the whole-plane kernel in `y` over `∂B_ρ(z)`, for every `x`. -/
theorem circleAverage_wholePlaneCov {z x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (fun y => wholePlaneCov x y) z ρ =
      logMaxAbs x + Real.circleAverage logMaxAbs z ρ - Real.log (max ρ ‖x - z‖) := by
  have hcongr : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere z |ρ|)]
      (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) := by
    refine Filter.eventually_of_mem (compl_singleton_mem_codiscreteWithin x) ?_
    intro y hy
    have hyx : x ≠ y := fun h => hy (h.symm ▸ rfl)
    show wholePlaneCov x y = _
    rw [wholePlaneCov_eq_of_ne hyx, norm_sub_rev]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hρ.ne']
  have hc1 : CircleIntegrable (fun y => logMaxAbs x + logMaxAbs y) z ρ :=
    ContinuousOn.circleIntegrable' (continuous_const.add logMaxAbs_continuous).continuousOn
  have hc2 : CircleIntegrable (fun y => Real.log ‖y - x‖) z ρ :=
    circleIntegrable_log_norm_sub_const ρ
  rw [show (fun y => logMaxAbs x + logMaxAbs y - Real.log ‖y - x‖) =
      (fun y => logMaxAbs x + logMaxAbs y) - (fun y => Real.log ‖y - x‖) from rfl,
    Real.circleAverage_sub hc1 hc2, show (fun y => logMaxAbs x + logMaxAbs y) =
      (fun _ => logMaxAbs x) + logMaxAbs from rfl,
    Real.circleAverage_add (circleIntegrable_const _ _ _)
      (ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn),
    Real.circleAverage_const, circleAverage_log_norm_sub_eq z x hρ, norm_sub_rev]
end S11uKernel

section S11iDilationMixing

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

/-- `|log r| ≤ 2 r^(-1/2)` for `0 < r ≤ 1`. -/
theorem abs_log_le_rpow_neg_half {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    |Real.log r| ≤ 2 * r ^ (-(1 / 2 : ℝ)) := by
  rw [abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  have h := Real.log_le_rpow_div (x := r⁻¹) (ε := 1 / 2) (by positivity) (by norm_num)
  rw [Real.log_inv, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le] at h
  linarith
/-- Pointwise bound for `log ‖·‖` on a ball of radius `T`, with the exponent `-1/2` (integrable in `ℂ`). -/
theorem norm_log_norm_le_rpow {T : ℝ} (hT : 0 < T) {x : ℂ} (hx : ‖x‖ < T) :
    ‖Real.log ‖x‖‖ ≤ (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]; simp
  set r := ‖x‖ with hr_def
  have hrpow : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hpos.le _
  have hX : 0 ≤ |Real.log T| * T ^ (1 / 2 : ℝ) := by positivity
  have hsplit : (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) =
      2 * r ^ (-(1 / 2 : ℝ)) + |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
  rw [Real.norm_eq_abs, hsplit]
  rcases le_total r 1 with h1 | h1
  · have := abs_log_le_rpow_neg_half hpos h1
    nlinarith [mul_nonneg hX hrpow]
  · have hlog : 0 ≤ Real.log r := Real.log_nonneg h1
    rw [abs_of_nonneg hlog]
    have hrT : r ≤ T := hx.le
    have hsq : r ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hpos.le hrT (by norm_num)
    have hone : 1 ≤ T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos _), one_mul]
      exact hsq
    have hlogT : Real.log r ≤ |Real.log T| := le_trans (Real.log_le_log hpos hrT) (le_abs_self _)
    have hmain : |Real.log T| ≤ |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) := by
      have := mul_nonneg (abs_nonneg (Real.log T)) (sub_nonneg.2 hone)
      nlinarith
    have e : |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) =
        |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hrpow]
/-- `log ‖·‖` is integrable on every ball of `ℂ` centred at `0`. -/
theorem integrableOn_log_norm_ball (T : ℝ) :
    IntegrableOn (fun w : ℂ => Real.log ‖w‖) (ball 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [ball_eq_empty.2 (by linarith : T ≤ 0)]
    exact integrableOn_empty
  · refine integrableOn_ball_of_norm_le_rpow (C := 2 + |Real.log T| * T ^ (1 / 2 : ℝ))
      (α := 1 / 2) ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      exact norm_log_norm_le_rpow hT (mem_ball_zero_iff.1 hx)
    · exact (Measurable.log measurable_norm).aestronglyMeasurable
/-- A test function is integrable on `ℂ`. -/
theorem integrable_of_isTestFunction {k : ℂ → ℝ} (hk : IsTestFunction univ k) : Integrable k :=
  hk.1.continuous.integrable_of_hasCompactSupport hk.2.1
/-- For a test function `k` supported in `closedBall 0 R`, `z ↦ k z * log ‖z - p‖` is integrable for every
centre `p` (translate of `integrableOn_log_norm_ball`, times a bounded factor). -/
theorem integrable_mul_log_norm_sub {k : ℂ → ℝ} (hk : IsTestFunction univ k) {R : ℝ}
    (hR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R) (p : ℂ) :
    Integrable (fun z => k z * Real.log ‖z - p‖) := by
  set T : ℝ := |R| + ‖p‖ + 1 with hT_def
  have hf0 : Integrable (Set.indicator (ball (0 : ℂ) T) fun w : ℂ => Real.log ‖w‖) :=
    (integrableOn_log_norm_ball T).integrable_indicator measurableSet_ball
  have hsh := hf0.comp_sub_right p
  obtain ⟨C, hC⟩ := hk.1.continuous.bounded_above_of_compact_support hk.2.1
  have hmain := hsh.bdd_mul hk.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  refine hmain.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hkz : k z = 0
  · simp [hkz]
  · have hz : ‖z‖ ≤ R := hR z hkz
    have hzp : z - p ∈ ball (0 : ℂ) T := by
      rw [mem_ball_zero_iff]
      have h1 : ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le _ _
      have h2 : R ≤ |R| := le_abs_self R
      have h3 : 0 ≤ |R| := abs_nonneg R
      linarith
    simp only [Set.indicator_of_mem hzp]
end S11iDilationMixing

section CircleDensityDoubleLog

open MeasureTheory Set Metric Filter Real
open scoped Topology Convolution

/-- The logarithmic potential of a continuous compactly supported planar
density is continuous. -/
theorem continuous_log_potential_of_compact_support {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fun w => ∫ x, g x * Real.log ‖x - w‖) := by
  have hl : LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) := by
    simpa using (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm (0 : ℂ))
  have hc := hgc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hg hl
  convert hc using 1
  funext w
  rw [MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with x
  change g x * Real.log ‖x - w‖ = g x * Real.log ‖w - x‖
  rw [norm_sub_rev]
end CircleDensityDoubleLog

section PairingCovarianceLinearity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The whole-plane covariance potential of a compactly supported continuous
function is continuous, without a normalization on its integral. -/
theorem continuous_wholePlaneCov_potential_general {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fun x => ∫ y, g y * wholePlaneCov x y) := by
  have heq : (fun x => ∫ y, g y * wholePlaneCov x y) =
      fun x => (∫ y, g y) * wholePlaneNormalization x +
        (∫ y, g y * wholePlaneNormalization y) -
          ∫ y, g y * Real.log ‖y - x‖ := by
    funext x
    have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
    have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
      (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
    have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
      have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
        ).integrable_smul_right_of_hasCompactSupport hg hgc
      simpa only [smul_eq_mul, mul_comm] using h
    have heq : (∫ y, g y * wholePlaneCov x y) =
        ∫ y, (g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) -
          g y * Real.log ‖y - x‖ := by
      apply integral_congr_ae
      filter_upwards [ae_ne_complex x] with y hy
      have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
      have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy',
        norm_sub_rev]
      simp only [wholePlaneNormalization]
      ring
    have hsum : (∫ y, g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) =
        (∫ y, g y * wholePlaneNormalization x) + ∫ y, g y * wholePlaneNormalization y :=
      integral_add (hgi.mul_const _) hni
    have hai : Integrable (fun y => g y * wholePlaneNormalization x +
        g y * wholePlaneNormalization y) := (hgi.mul_const _).add hni
    rw [heq, integral_sub hai hli, hsum, integral_mul_const]
  rw [heq]
  exact ((continuous_const.mul continuous_wholePlaneNormalization).add continuous_const).sub
    (continuous_log_potential_of_compact_support hg hgc)
end PairingCovarianceLinearity

section AffineCore

open MeasureTheory Complex

/-- Affine change of variables on `ℂ`: `∫ g (a u + b) du = |a|⁻² ∫ g` for `a ≠ 0`. -/
theorem integral_affine_complex {a : ℂ} (ha : a ≠ 0) (b : ℂ) (g : ℂ → ℝ) :
    ∫ u, g (a * u + b) = (‖a‖ ^ 2)⁻¹ * ∫ x, g x := by
  have hae : a = (‖a‖ : ℂ) * ((Circle.exp (arg a) : Circle) : ℂ) := by
    rw [Circle.coe_exp]
    exact (Complex.norm_mul_exp_arg_mul_I a).symm
  set e : Circle := Circle.exp (arg a) with he
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  generalize hR : ‖a‖ = r at hae hr ⊢
  -- the map `u ↦ a u + b` is `u ↦ r • (rotation e u) + b` (rotation: a unit complex multiplication)
  have hG : (fun u : ℂ => g (a * u + b)) = fun u => g (r • rotation e u + b) := by
    funext u
    rw [rotation_apply, Complex.real_smul, hae]
    congr 1
    ring
  have hmp : ∫ u, g (r • rotation e u + b) = ∫ v, g (r • v + b) :=
    (rotation e).measurePreserving.integral_comp (rotation e).toHomeomorph.measurableEmbedding
      (fun v => g (r • v + b))
  have hscale := Measure.integral_comp_smul volume (fun y : ℂ => g (y + b)) r
  have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [hfin, abs_of_pos (inv_pos.2 (pow_pos hr 2))] at hscale
  simp only [smul_eq_mul, integral_add_right_eq_self g b] at hscale
  rw [hG, hmp]
  exact hscale
/-- Reparametrisation of a circle average under `z ↦ a z + b`:
`avg_{∂B(a z + b, |a| ρ)} f = avg_{∂B(z, ρ)} (f ∘ F)`. -/
theorem circleAverage_affine_comp {a : ℂ} (b : ℂ) (f : ℂ → ℝ) (z : ℂ) (ρ : ℝ) :
    Real.circleAverage f (a * z + b) (‖a‖ * ρ) = Real.circleAverage (fun x => f (a * x + b)) z ρ := by
  have hae : (‖a‖ : ℂ) * exp (arg a * I) = a := Complex.norm_mul_exp_arg_mul_I a
  have key : ∀ θ : ℝ, a * circleMap z ρ θ + b = circleMap (a * z + b) (‖a‖ * ρ) (θ + arg a) := by
    intro θ
    simp only [circleMap]
    push_cast
    rw [add_mul, Complex.exp_add]
    linear_combination (-((ρ : ℂ) * exp (θ * I))) * hae
  have hper : Function.Periodic (fun θ : ℝ => f (circleMap (a * z + b) (‖a‖ * ρ) θ)) (2 * Real.pi) :=
    (periodic_circleMap (a * z + b) (‖a‖ * ρ)).comp f
  have h2 : ∫ x in (0 : ℝ)..2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) (x + arg a)) =
      ∫ x in arg a..arg a + 2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) := by
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => f (circleMap (a * z + b) (‖a‖ * ρ) x)) (arg a),
      zero_add, add_comm (2 * Real.pi) (arg a)]
  have h3 : ∫ x in arg a..arg a + 2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) =
      ∫ x in (0 : ℝ)..2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) := by
    have := hper.intervalIntegral_add_eq (arg a) 0
    simpa only [zero_add, add_zero] using this
  have hRHS : ∀ θ : ℝ, (fun x => f (a * x + b)) (circleMap z ρ θ) =
      f (circleMap (a * z + b) (‖a‖ * ρ) (θ + arg a)) := fun θ => by
    simp only
    rw [key θ]
  unfold Real.circleAverage
  congr 1
  simp only [hRHS]
  exact (h2.trans h3).symm
/-- Pairings: `|a|⁻² ⟨φ ∘ F⁻¹, f⟩ = ⟨φ, f ∘ F⟩` for every `f` (no integrability needed). -/
theorem smear_affine_pairing {a : ℂ} (ha : a ≠ 0) (b : ℂ) (φ f : ℂ → ℝ) :
    (‖a‖ ^ 2)⁻¹ * (GFFObservable.pairing (fun y => φ ((y - b) / a))).smear f =
      (GFFObservable.pairing φ).smear (fun x => f (a * x + b)) := by
  have h : ∫ u, φ u * f (a * u + b) = (‖a‖ ^ 2)⁻¹ * ∫ x, φ ((x - b) / a) * f x := by
    have := integral_affine_complex ha b (fun x => φ ((x - b) / a) * f x)
    simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ ha] using this
  simp only [GFFObservable.smear]
  rw [h]
/-- Circles: `⟨circle(|a| r, a z + b), f⟩ - ⟨circle(|a|, b), f⟩ = ⟨circle(r, z), f ∘ F⟩ - ⟨circle(1, 0), f ∘ F⟩`
(the centring of `hcirc` at `(|a|, b)` is the centring at the unit circle after pull-back). -/
theorem smear_affine_circle_sub {a : ℂ} (b z : ℂ) (r : ℝ) (f : ℂ → ℝ) :
    (GFFObservable.circle (‖a‖ * r) (a * z + b)).smear f - (GFFObservable.circle ‖a‖ b).smear f =
      (GFFObservable.circle r z).smear (fun x => f (a * x + b)) -
        (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  have h0 : (GFFObservable.circle ‖a‖ b).smear f = (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
    have := circleAverage_affine_comp (a := a) b f 0 1
    simp only [mul_one, mul_zero, zero_add] at this
    exact this
  have h1 : (GFFObservable.circle (‖a‖ * r) (a * z + b)).smear f =
      (GFFObservable.circle r z).smear (fun x => f (a * x + b)) :=
    circleAverage_affine_comp (a := a) b f z r
  rw [h0, h1]
end AffineCore

section AffineKernel

open MeasureTheory Filter Set Metric Topology

/-- The unit-circle average of `L ∘ F`, `A = avg_{∂B(0,1)} log max(|a v + b|, 1)`. -/
noncomputable def affA (a b : ℂ) : ℝ :=
  Real.circleAverage (fun v => logMaxAbs (a * v + b)) 0 1
/-- The pointwise pull-back of the log-potential, `M(x) = L(F x) - L(x) + A - log |a|`. -/
noncomputable def affM (a b : ℂ) (x : ℂ) : ℝ :=
  logMaxAbs (a * x + b) - logMaxAbs x + affA a b - Real.log ‖a‖
/-- The constant `M0 = 2A - log |a|`. -/
noncomputable def affM0 (a b : ℂ) : ℝ :=
  2 * affA a b - Real.log ‖a‖
/-- **Pointwise affine identity** of the whole-plane kernel off the diagonal:
`K(F x, F y) = K(x, y) + M x + M y - M0`. -/
theorem wholePlaneCov_affine {a : ℂ} (ha : a ≠ 0) (b : ℂ) {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov (a * x + b) (a * y + b) =
      wholePlaneCov x y + affM a b x + affM a b y - affM0 a b := by
  have hs : 0 < ‖a‖ := norm_pos_iff.2 ha
  have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hd : ‖a * x + b - (a * y + b)‖ = ‖a‖ * ‖x - y‖ := by
    rw [show a * x + b - (a * y + b) = a * (x - y) by ring, norm_mul]
  have hL : ∀ z : ℂ, 0 < max ‖z‖ 1 := fun z => lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold wholePlaneCov affM affM0 logMaxAbs
  rw [hd, Real.log_div (mul_pos (hL _) (hL _)).ne' (mul_pos hs ht).ne',
    Real.log_mul (hL _).ne' (hL _).ne', Real.log_mul hs.ne' ht.ne',
    Real.log_div (mul_pos (hL _) (hL _)).ne' ht.ne', Real.log_mul (hL _).ne' (hL _).ne']
  ring
/-- The unit-circle average of `L` vanishes. -/
theorem circleAverage_logMaxAbs_unit : Real.circleAverage logMaxAbs 0 1 = 0 := by
  have h : Real.circleAverage logMaxAbs 0 1 = Real.circleAverage (fun _ => (0 : ℝ)) 0 1 := by
    refine Real.circleAverage_congr_sphere (fun y hy => ?_)
    have hy1 : ‖y‖ = 1 := by simpa using hy
    simp [logMaxAbs, hy1]
  rw [h, Real.circleAverage_const]
/-- The unit-circle average of the kernel vanishes at every point: `avg_{∂B(0,1)} K(x, ·) = 0`. -/
theorem circleAverage_wholePlaneCov_unit (x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 1 = 0 := by
  rw [circleAverage_wholePlaneCov one_pos, circleAverage_logMaxAbs_unit]
  simp only [logMaxAbs, sub_zero, add_zero, max_comm 1 ‖x‖, sub_self]
/-- The unit-circle average of `M` is `M0`: `avg_{∂B(0,1)} M = M0`. -/
theorem circleAverage_affM_unit (a b : ℂ) : Real.circleAverage (affM a b) 0 1 = affM0 a b := by
  have hc1 : CircleIntegrable (fun y => logMaxAbs (a * y + b)) 0 1 :=
    ContinuousOn.circleIntegrable' (logMaxAbs_continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hc2 : CircleIntegrable (fun y => logMaxAbs y) 0 1 :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have hc3 : CircleIntegrable (fun _ : ℂ => affA a b - Real.log ‖a‖) 0 1 :=
    circleIntegrable_const _ _ _
  have hfun : affM a b = fun y => (logMaxAbs (a * y + b) - logMaxAbs y) + (affA a b - Real.log ‖a‖) :=
    funext fun y => by unfold affM; ring
  have hc12 : CircleIntegrable (fun y => logMaxAbs (a * y + b) - logMaxAbs y) 0 1 := hc1.sub hc2
  rw [hfun, Real.circleAverage_fun_add hc12 hc3, Real.circleAverage_fun_sub hc1 hc2,
    Real.circleAverage_const, circleAverage_logMaxAbs_unit]
  unfold affM0
  have : Real.circleAverage (fun y => logMaxAbs (a * y + b)) 0 1 = affA a b := rfl
  rw [this]
  ring
/-- Continuity of the pairing potential `x ↦ ∫ ψ(y) K(x, y) dy` for a test function `ψ`. -/
theorem continuous_potential_pairing {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) :
    Continuous (fun x => (GFFObservable.pairing ψ).smear (fun y => wholePlaneCov x y)) :=
  continuous_wholePlaneCov_potential_general hψ.1.continuous hψ.2.1
/-- Continuity of the circle potential `x ↦ avg_{∂B(z, r)} K(x, ·)` for `r > 0`. -/
theorem continuous_potential_circle {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x => (GFFObservable.circle r z).smear (fun y => wholePlaneCov x y)) := by
  have h : (fun x => (GFFObservable.circle r z).smear (fun y => wholePlaneCov x y)) =
      fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - Real.log (max r ‖x - z‖) :=
    funext fun x => circleAverage_wholePlaneCov hr
  rw [h]
  have hmax : ∀ x : ℂ, max r ‖x - z‖ ≠ 0 := fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne'
  exact (logMaxAbs_continuous.add continuous_const).sub
    (Continuous.log (by fun_prop) hmax)
/-- Continuity of the smeared potential of every admissible observable. -/
theorem continuous_potential {q : GFFObservable} (hq : q.IsAdmissible) :
    Continuous (fun x => q.smear (fun y => wholePlaneCov x y)) := by
  cases q with
  | pairing ψ => exact continuous_potential_pairing hq
  | circle r z => exact continuous_potential_circle hq z
/-- `M` is continuous. -/
theorem continuous_affM (a b : ℂ) : Continuous (affM a b) := by
  unfold affM
  exact ((logMaxAbs_continuous.comp (by fun_prop)).sub logMaxAbs_continuous).add continuous_const |>.sub
    continuous_const
/-- Circle case of the affine potential identity: the circle average over `∂B(z, r)` of `K(F x, F ·)`. -/
theorem circleAverage_potential_affine {a : ℂ} (ha : a ≠ 0) (b x z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun y => wholePlaneCov (a * x + b) (a * y + b)) z r =
      Real.circleAverage (fun y => wholePlaneCov x y) z r + affM a b x +
        Real.circleAverage (affM a b) z r - affM0 a b := by
  have hcongr : (fun y => wholePlaneCov (a * x + b) (a * y + b)) =ᶠ[codiscreteWithin (sphere z |r|)]
      (fun y => (logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖) + affM a b x + affM a b y - affM0 a b) := by
    refine Filter.eventually_of_mem (compl_singleton_mem_codiscreteWithin x) ?_
    intro y hy
    have hxy : x ≠ y := fun h => hy (Set.mem_singleton_iff.2 h.symm)
    show wholePlaneCov (a * x + b) (a * y + b) = _
    rw [wholePlaneCov_affine ha b hxy, wholePlaneCov_eq_of_ne hxy]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hr.ne']
  have i1 : CircleIntegrable (fun y => logMaxAbs y) z r :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have i2 : CircleIntegrable (fun y => Real.log ‖x - y‖) z r := by
    have := circleIntegrable_log_norm_sub_const (c := z) (a := x) r
    simpa only [norm_sub_rev] using this
  have hlog : Real.circleAverage (fun y => Real.log ‖x - y‖) z r = Real.log (max r ‖x - z‖) := by
    rw [show (fun y => Real.log ‖x - y‖) = fun y => Real.log ‖y - x‖ from funext fun y => by rw [norm_sub_rev],
      circleAverage_log_norm_sub_eq z x hr, norm_sub_rev z x]
  have iM : CircleIntegrable (affM a b) z r := (continuous_affM a b).continuousOn.circleIntegrable'
  have hfun : (fun y => (logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖) + affM a b x + affM a b y - affM0 a b) =
      fun y => ((logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y + affM a b y) - Real.log ‖x - y‖ :=
    funext fun y => by ring
  have hc0 : CircleIntegrable (fun _ : ℂ => logMaxAbs x + affM a b x - affM0 a b) z r :=
    circleIntegrable_const _ _ _
  have hs1 : CircleIntegrable (fun y => (logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y) z r :=
    hc0.fun_add i1
  have hs2 : CircleIntegrable (fun y => ((logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y) + affM a b y)
      z r := hs1.fun_add iM
  rw [hfun, Real.circleAverage_fun_sub hs2 i2, Real.circleAverage_fun_add hs1 iM,
    Real.circleAverage_fun_add hc0 i1, Real.circleAverage_const, hlog, circleAverage_wholePlaneCov hr]
  unfold affM0
  ring
/-- A test function times a continuous function is integrable. -/
theorem integrable_test_mul_continuous {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) {g : ℂ → ℝ}
    (hg : Continuous g) : Integrable (fun y => ψ y * g y) :=
  (hψ.1.continuous.mul hg).integrable_of_hasCompactSupport hψ.2.1.mul_right
/-- Pairing case of the affine potential identity:
`∫ ψ(y) K(F x, F y) dy = ∫ ψ(y) K(x, y) dy + (∫ ψ) M x + ∫ ψ M - (∫ ψ) M0`. -/
theorem integral_potential_affine_pairing {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction univ ψ) :
    ∫ y, ψ y * wholePlaneCov (a * x + b) (a * y + b) =
      (∫ y, ψ y * wholePlaneCov x y) + (∫ y, ψ y) * affM a b x + (∫ y, ψ y * affM a b y) -
        (∫ y, ψ y) * affM0 a b := by
  obtain ⟨R, hR⟩ := hψ.2.1.isCompact.isBounded.subset_closedBall 0
  have hψi : Integrable ψ := integrable_of_isTestFunction hψ
  have hMi : Integrable (fun y => ψ y * affM a b y) := integrable_test_mul_continuous hψ (continuous_affM a b)
  have hLi : Integrable (fun y => ψ y * logMaxAbs y) :=
    integrable_test_mul_continuous hψ logMaxAbs_continuous
  have hlog : Integrable (fun y => ψ y * Real.log ‖x - y‖) := by
    have h := integrable_mul_log_norm_sub hψ (R := R) (fun z hz => by
      have := hR (subset_tsupport ψ hz)
      simpa using this) x
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_sub_rev]
  have hKi : Integrable (fun y => ψ y * wholePlaneCov x y) := by
    have h := ((hψi.mul_const (logMaxAbs x)).add hLi).sub hlog
    refine h.congr ?_
    filter_upwards [Measure.ae_ne volume x] with y hy
    rw [wholePlaneCov_eq_of_ne hy.symm]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hae : (fun y => ψ y * wholePlaneCov (a * x + b) (a * y + b)) =ᵐ[volume]
      (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x + ψ y * affM a b y - ψ y * affM0 a b) := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    rw [wholePlaneCov_affine ha b hy.symm]
    ring
  have I1 : Integrable (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x) :=
    hKi.add (hψi.mul_const _)
  have I2 : Integrable (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x + ψ y * affM a b y) :=
    I1.add hMi
  have I3 : Integrable (fun y => ψ y * affM0 a b) := hψi.mul_const _
  rw [integral_congr_ae hae, integral_sub I2 I3, integral_add I1 hMi, integral_add hKi (hψi.mul_const _)]
  simp only [integral_mul_const]
end AffineKernel

section AffineAlg

open scoped ContDiff
open MeasureTheory Filter Set Metric Topology

/-- Pull-back of an observable by `F z = a z + b`: a pairing `φ` becomes `φ ∘ F⁻¹`; a circle average `(r, z)`
becomes the circle average `(|a| r, F z)`. -/
noncomputable def affP (a b : ℂ) : GFFObservable → GFFObservable
  | .pairing φ => .pairing (fun y => φ ((y - b) / a))
  | .circle r z => .circle (‖a‖ * r) (a * z + b)
/-- Coefficient of the pulled-back observable: `|a|⁻²` for a pairing (Jacobian), `1` for a circle average. -/
noncomputable def affC (a : ℂ) : GFFObservable → ℝ
  | .pairing _ => (‖a‖ ^ 2)⁻¹
  | .circle _ _ => 1
/-- Smearing against the circle average of the base point `b` in the original coordinates. -/
theorem smear_circle_affine_base {a : ℂ} (b : ℂ) (f : ℂ → ℝ) :
    (GFFObservable.circle ‖a‖ b).smear f = (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  have := circleAverage_affine_comp (a := a) b f 0 1
  simp only [mul_one, mul_zero, zero_add] at this
  exact this
/-- **Core change of variables.** For every observable `o` and every function `f` (no integrability needed):
`affC a o · (affP a b o)[f] - m_o · (circle |a| b)[f] = o[f ∘ F] - m_o · (circle 1 0)[f ∘ F]`, where `m_o = o[1]`. -/
theorem smear_affine_core {a : ℂ} (ha : a ≠ 0) (b : ℂ) (o : GFFObservable) (f : ℂ → ℝ) :
    affC a o * (affP a b o).smear f - (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear f =
      o.smear (fun x => f (a * x + b)) -
        (o.smear fun _ => 1) * (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  cases o with
  | pairing φ =>
    have h := smear_affine_pairing ha b φ f
    have hb := smear_circle_affine_base (a := a) b f
    simp only [affC, affP]
    linear_combination h - (GFFObservable.pairing φ).smear (fun _ => 1) * hb
  | circle r z =>
    have h := smear_affine_circle_sub (a := a) b z r f
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    simp only [affC, affP]
    rw [hm, one_mul, one_mul]
    linear_combination h
/-- Linear combinations of smearing functionals against continuous functions (`o` admissible). -/
theorem smear_lincomb {q : GFFObservable} (hq : q.IsAdmissible) {g₁ g₂ : ℂ → ℝ} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (α β : ℝ) :
    q.smear (fun x => α * g₁ x + β * g₂ x) = α * q.smear g₁ + β * q.smear g₂ := by
  cases q with
  | pairing ψ =>
    have i1 := (integrable_test_mul_continuous hq h₁).const_mul α
    have i2 := (integrable_test_mul_continuous hq h₂).const_mul β
    simp only [GFFObservable.smear]
    rw [show (fun x => ψ x * (α * g₁ x + β * g₂ x)) = fun x => α * (ψ x * g₁ x) + β * (ψ x * g₂ x) from
      funext fun x => by ring, integral_add i1 i2, integral_const_mul, integral_const_mul]
  | circle r z =>
    have hr : 0 < r := hq
    have c1 : CircleIntegrable (fun x => α * g₁ x) z r :=
      ((continuous_const.mul h₁).continuousOn).circleIntegrable'
    have c2 : CircleIntegrable (fun x => β * g₂ x) z r :=
      ((continuous_const.mul h₂).continuousOn).circleIntegrable'
    show Real.circleAverage (fun x => α * g₁ x + β * g₂ x) z r = _
    rw [Real.circleAverage_fun_add c1 c2]
    have e1 : Real.circleAverage (fun x => α * g₁ x) z r = α * Real.circleAverage g₁ z r := by
      rw [show (fun x => α * g₁ x) = fun x => α • g₁ x from rfl, Real.circleAverage_fun_smul, smul_eq_mul]
    have e2 : Real.circleAverage (fun x => β * g₂ x) z r = β * Real.circleAverage g₂ z r := by
      rw [show (fun x => β * g₂ x) = fun x => β • g₂ x from rfl, Real.circleAverage_fun_smul, smul_eq_mul]
    rw [e1, e2]
    rfl
/-- Adding a constant: `q[g + c] = q[g] + c · q[1]`. -/
theorem smear_add_const {q : GFFObservable} (hq : q.IsAdmissible) {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) :
    q.smear (fun x => g x + c) = q.smear g + c * q.smear (fun _ => 1) := by
  have h := smear_lincomb (g₂ := fun _ : ℂ => (1 : ℝ)) hq hg continuous_const 1 c
  simp only [one_mul, mul_one] at h
  exact h
/-- Composition with the affine map `y ↦ (y - b)/a` preserves test functions. -/
theorem isTestFunction_affine {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsTestFunction univ (fun y => φ ((y - b) / a)) := by
  obtain ⟨h1, h2, -⟩ := hφ
  let H : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-b)).trans (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha))
  have e : (fun y => φ ((y - b) / a)) = φ ∘ H := by
    funext y
    change φ ((y - b) / a) = φ (a⁻¹ * (y + -b))
    congr 1
    ring
  refine ⟨?_, ?_, subset_univ _⟩
  · rw [e]
    refine h1.comp ?_
    show ContDiff ℝ ∞ (fun y : ℂ => a⁻¹ * (y + -b))
    fun_prop
  · rw [e]
    exact h2.comp_homeomorph H
/-- The pulled-back observable is admissible. -/
theorem isAdmissible_affP {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o : GFFObservable} (ho : o.IsAdmissible) :
    (affP a b o).IsAdmissible := by
  cases o with
  | pairing φ => exact isTestFunction_affine ho ha b
  | circle r z => exact mul_pos (norm_pos_iff.2 ha) ho
/-- The potential of an admissible observable transforms as the kernel at `F x` (smeared form). -/
theorem smear_potential_affine {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {q : GFFObservable} (hq : q.IsAdmissible) :
    q.smear (fun y => wholePlaneCov (a * x + b) (a * y + b)) =
      q.smear (fun y => wholePlaneCov x y) + (q.smear fun _ => 1) * affM a b x + q.smear (affM a b) -
        (q.smear fun _ => 1) * affM0 a b := by
  cases q with
  | pairing ψ =>
    have h := integral_potential_affine_pairing ha b x hq
    simp only [GFFObservable.smear, mul_one]
    exact h
  | circle r z =>
    have hr : 0 < r := hq
    have h := circleAverage_potential_affine ha b x z hr
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    rw [hm, one_mul, one_mul]
    exact h
/-- The transformed potential at `F x`: the kernel potential of `o'` at `x`, up to a constant. -/
theorem transformed_potential_affine {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {o' : GFFObservable} (ho' : o'.IsAdmissible) :
    affC a o' * (affP a b o').smear (fun w => wholePlaneCov (a * x + b) w) -
        (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear (fun w => wholePlaneCov (a * x + b) w) =
      o'.smear (fun y => wholePlaneCov x y) + (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b) := by
  have hcore := smear_affine_core ha b o' (fun w => wholePlaneCov (a * x + b) w)
  beta_reduce at hcore
  have hC1 : (GFFObservable.circle 1 0).IsAdmissible := one_pos
  rw [hcore, smear_potential_affine ha b x ho', smear_potential_affine ha b x hC1]
  have hC1K : (GFFObservable.circle 1 0).smear (fun y => wholePlaneCov x y) = 0 :=
    circleAverage_wholePlaneCov_unit x
  have hC1M : (GFFObservable.circle 1 0).smear (affM a b) = affM0 a b := circleAverage_affM_unit a b
  have hC1one : (GFFObservable.circle 1 0).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) 0 1
  rw [hC1K, hC1M, hC1one]
  ring
/-- **Deterministic covariance identity of the affine pull-back.** For admissible `o, o'` the bilinear expansion of
`cov(T o, T o')`, with `T o = affC · affP - mass(o) · circle |a| b`, equals `B(o, o') - mass(o) B(circle 1 0, o')`. -/
theorem cov_det_identity {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o o' : GFFObservable} (ho : o.IsAdmissible)
    (ho' : o'.IsAdmissible) :
    affC a o * affC a o' * wholePlaneGFFCov (affP a b o) (affP a b o') -
        affC a o * (o'.smear fun _ => 1) * wholePlaneGFFCov (affP a b o) (GFFObservable.circle ‖a‖ b) -
      (o.smear fun _ => 1) * affC a o' * wholePlaneGFFCov (GFFObservable.circle ‖a‖ b) (affP a b o') +
        (o.smear fun _ => 1) * (o'.smear fun _ => 1) *
          wholePlaneGFFCov (GFFObservable.circle ‖a‖ b) (GFFObservable.circle ‖a‖ b) =
      wholePlaneGFFCov o o' - (o.smear fun _ => 1) * wholePlaneGFFCov (GFFObservable.circle 1 0) o' := by
  unfold wholePlaneGFFCov
  have hpo : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hp' : (affP a b o').IsAdmissible := isAdmissible_affP ha b ho'
  have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  have cP : Continuous (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) :=
    continuous_potential hp'
  have cS : Continuous (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    continuous_potential hS
  have hA : Continuous (fun x => o'.smear (fun y => wholePlaneCov x y)) := continuous_potential ho'
  set G : ℂ → ℝ := fun w => affC a o' * (affP a b o').smear (fun y => wholePlaneCov w y) -
    (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y) with hG
  have hGeq : G = fun w => affC a o' * (affP a b o').smear (fun y => wholePlaneCov w y) +
      (-(o'.smear fun _ => 1)) * (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y) :=
    funext fun w => by simp only [hG]; ring
  have s1 : (affP a b o).smear G =
      affC a o' * (affP a b o).smear (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) +
        (-(o'.smear fun _ => 1)) *
          (affP a b o).smear (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    by rw [hGeq]; exact smear_lincomb hpo cP cS _ _
  have s2 : (GFFObservable.circle ‖a‖ b).smear G =
      affC a o' * (GFFObservable.circle ‖a‖ b).smear (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) +
        (-(o'.smear fun _ => 1)) *
          (GFFObservable.circle ‖a‖ b).smear (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    by rw [hGeq]; exact smear_lincomb hS cP cS _ _
  have hcore := smear_affine_core ha b o G
  have hGF : (fun x => G (a * x + b)) = fun x =>
      o'.smear (fun y => wholePlaneCov x y) + (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b) :=
    funext fun x => transformed_potential_affine ha b x ho'
  rw [hGF] at hcore
  have hC1 : (GFFObservable.circle 1 0).IsAdmissible := one_pos
  have hc0 := smear_add_const ho hA (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b)
  have hc1 := smear_add_const hC1 hA (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b)
  have hC1one : (GFFObservable.circle 1 0).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) 0 1
  beta_reduce at hc0 hc1
  rw [hc0, hc1, hC1one] at hcore
  linear_combination hcore - affC a o * s1 + (o.smear fun _ => 1) * s2
end AffineAlg

section Affine

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The value of a transformed observable in terms of the original field (`affP`, `affC`, mass). -/
theorem eval_affine {a : ℂ} (b : ℂ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ)
    (o : GFFObservable) :
    o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC (fun y => φ ((y - b) / a)) - hcirc ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc (‖a‖ * r) (a * z + b) - hcirc ‖a‖ b) =
      affC a o * (affP a b o).eval hC hcirc - (o.smear fun _ => 1) * hcirc ‖a‖ b := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.eval, affC, affP, GFFObservable.smear, mul_one]
    ring
  | circle r z =>
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    simp only [GFFObservable.eval, affC, affP]
    rw [hm]
    ring
/-- A covariance of two linear combinations of four variables, expanded bilinearly. -/
theorem cov_sub_mul_sub {P : Measure Ω} [IsFiniteMeasure P] {X₁ X₂ Y₁ Y₂ : Ω → ℝ} (c m d n : ℝ)
    (h₁ : MemLp X₁ 2 P) (h₂ : MemLp X₂ 2 P) (k₁ : MemLp Y₁ 2 P) (k₂ : MemLp Y₂ 2 P) :
    cov[fun ω => c * X₁ ω - m * X₂ ω, fun ω => d * Y₁ ω - n * Y₂ ω; P] =
      c * d * cov[X₁, Y₁; P] - c * n * cov[X₁, Y₂; P] - m * d * cov[X₂, Y₁; P] + m * n * cov[X₂, Y₂; P] := by
  have kk : MemLp (fun ω => d * Y₁ ω - n * Y₂ ω) 2 P := (k₁.const_mul d).sub (k₂.const_mul n)
  rw [covariance_fun_sub_left (h₁.const_mul c) (h₂.const_mul m) kk,
    covariance_fun_sub_right (h₁.const_mul c) (k₁.const_mul d) (k₂.const_mul n),
    covariance_fun_sub_right (h₂.const_mul m) (k₁.const_mul d) (k₂.const_mul n)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring
/-- A variable that vanishes almost surely has zero covariance with anything. -/
theorem covariance_eq_zero_of_ae_zero {P : Measure Ω} {X Y : Ω → ℝ} (hX : X =ᵐ[P] 0) :
    cov[X, Y; P] = 0 := by
  have hEX : P[X] = 0 := by
    rw [integral_congr_ae hX]
    simp
  have hint : (fun ω => (X ω - P[X]) * (Y ω - P[Y])) =ᵐ[P] 0 := by
    filter_upwards [hX] with ω hω
    simp [hEX, hω]
  unfold covariance
  rw [integral_congr_ae hint]
  simp
/-- Gaussian second moments of the observables of a whole-plane GFF. -/
theorem memLp_two_obs {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {o : GFFObservable} (ho : o.IsAdmissible) :
    MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
  (hG.isGaussianProcess.hasGaussianLaw_eval (⟨o, ho⟩ : GFFObservable.Admissible)).memLp
    (by norm_num)
/-- The unit-circle average of a whole-plane GFF is orthogonal to every observable (a.s. zero). -/
theorem cov_circle_one_zero {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {o : GFFObservable} (ho : o.IsAdmissible) :
    wholePlaneGFFCov (GFFObservable.circle 1 0) o = 0 := by
  have h := hG.covariance_eq (GFFObservable.circle 1 0) o one_pos ho
  rw [← h]
  apply covariance_eq_zero_of_ae_zero
  exact IsWholePlaneGFF.ae_circleAverage_one_zero hG
omit [MeasurableSpace Ω] in
/-- The transformed observable at `ω`, as a combination of the original ones (pointwise in `ω`). -/
theorem eval_affine_fun {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {a : ℂ} (b : ℂ)
    (o : GFFObservable) (ω : Ω) :
    o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) =
      affC a o * (affP a b o).eval (hC ω) (hcirc ω) -
        (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
  eval_affine b (hC ω) (hcirc ω) o
/-- The Gaussian clause of the transformed field. -/
theorem isGaussianProcess_affine {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsGaussianProcess (fun (t : GFFObservable.Admissible) ω =>
      t.1.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) P := by
  classical
  apply IsGaussianProcess.of_isGaussianProcess hG.isGaussianProcess
  rintro ⟨o, ho⟩
  have hp : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hs : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  let I : Finset GFFObservable.Admissible := {⟨affP a b o, hp⟩, ⟨GFFObservable.circle ‖a‖ b, hs⟩}
  refine ⟨I, affC a o • ContinuousLinearMap.proj
      (⟨⟨affP a b o, hp⟩, Finset.mem_insert_self _ _⟩ : I) -
      (o.smear fun _ => 1) • ContinuousLinearMap.proj
      (⟨⟨GFFObservable.circle ‖a‖ b, hs⟩, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ : I),
    fun ω => ?_⟩
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact eval_affine_fun b o ω
/-- The covariance clause of the transformed field, from the deterministic identity. -/
theorem covariance_affine {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o o' : GFFObservable}
    (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    cov[fun ω => o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b),
      fun ω => o'.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b); P] =
      wholePlaneGFFCov o o' := by
  have := hG.isGaussianProcess.isProbabilityMeasure
  have hp : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hp' : (affP a b o').IsAdmissible := isAdmissible_affP ha b ho'
  have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  have e1 : (fun ω => o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) =
      fun ω => affC a o * (affP a b o).eval (hC ω) (hcirc ω) -
        (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
    funext fun ω => eval_affine_fun b o ω
  have e2 : (fun ω => o'.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) =
      fun ω => affC a o' * (affP a b o').eval (hC ω) (hcirc ω) -
        (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
    funext fun ω => eval_affine_fun b o' ω
  rw [e1, e2, cov_sub_mul_sub _ _ _ _ (memLp_two_obs hG hp) (memLp_two_obs hG hS)
    (memLp_two_obs hG hp') (memLp_two_obs hG hS),
    hG.covariance_eq _ _ hp hp', hG.covariance_eq _ _ hp hS, hG.covariance_eq _ _ hS hp',
    hG.covariance_eq _ _ hS hS]
  have hdet := cov_det_identity ha b ho ho'
  have hB := cov_circle_one_zero hG ho'
  linear_combination hdet - (o.smear fun _ => 1) * hB
end Affine

/-- **Affine invariance of the whole-plane GFF, LP form** (as in arXiv:2208.11795). For a whole-plane GFF
`(hC, hcirc)` and `a ∈ ℂ ∖ {0}`, `b ∈ ℂ`, the pairings `φ ↦ |a|⁻² hC(φ ∘ F⁻¹) - hcirc |a| b · ∫ φ` and the circle
averages `(r, z) ↦ hcirc (|a| r) (a z + b) - hcirc |a| b`, where `F z = a z + b`, again form a whole-plane GFF. -/
def WholePlaneGFFAffineInvarianceLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)

/-- **`WholePlaneGFFAffineInvarianceLP` is a theorem** (adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]). Derived from `IsWholePlaneGFF` alone, with no hypothesis beyond it. -/
theorem wholePlaneGFFAffineInvariance_lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    WholePlaneGFFAffineInvarianceLP P hC hcirc := by
  intro hG a ha b
  have := hG.isGaussianProcess.isProbabilityMeasure
  refine
    { measurable_pairing := ?_
      measurable_circle := ?_
      isGaussianProcess := isGaussianProcess_affine hG ha b
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := ?_ }
  · intro φ hφ
    exact ((hG.measurable_pairing _ (isTestFunction_affine hφ ha b)).const_mul _).sub
      ((hG.measurable_circle ‖a‖ b (norm_pos_iff.2 ha)).mul_const _)
  · intro r z hr
    exact (hG.measurable_circle (‖a‖ * r) (a * z + b) (mul_pos (norm_pos_iff.2 ha) hr)).sub
      (hG.measurable_circle ‖a‖ b (norm_pos_iff.2 ha))
  · intro o ho
    have hp := isAdmissible_affP ha b ho
    have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
    have hint1 := ((memLp_two_obs hG hp).integrable one_le_two).const_mul (affC a o)
    have hint2 := ((memLp_two_obs hG hS).integrable one_le_two).const_mul (o.smear fun _ => 1)
    simp only [eval_affine_fun b o]
    rw [integral_sub hint1 hint2, integral_const_mul, integral_const_mul,
      hG.integral_eq_zero _ hp, hG.integral_eq_zero _ hS]
    ring
  · intro o o' ho ho'
    exact covariance_affine hG ha b ho ho'
  · filter_upwards [hG.ae_continuousOn_circle] with ω hω
    have hmap : MapsTo (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
      fun p hp => ⟨mul_pos (norm_pos_iff.2 ha) hp.1, mem_univ _⟩
    have hcont : Continuous (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) := by fun_prop
    exact (hω.comp hcont.continuousOn hmap).sub continuousOn_const
end LatticeProb.LQG.AffineDerived
