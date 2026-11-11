import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import LatticeProb.Analysis.DistributionalLaplacian
import LatticeProb.Bonanno.LQGMetric.Field.CircleParameter
import LatticeProb.Bonanno.LQGMetric.Field.WholePlaneCov
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgVersion
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux

/-!
# Circle averages of the whole-plane covariance kernel

For the whole-plane Gaussian free field with covariance kernel `wholePlaneCov`, normalised so that its average
over the unit circle vanishes (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Section 3.1, eq. (3.2)), this file computes the circle averages of the kernel: the logarithmic mean value property
`∮ log ‖w - z‖ = log max(r, ‖z‖)` on a circle centred at `0`, the circle average of `wholePlaneCov z ·`, and the
circle-circle covariance `∮_{∂B_s} ∮_{∂B_r} wholePlaneCov z w`.

References: Armitage–Gardiner, *Classical Potential Theory*, Springer 2001, Section 3.1 (logarithmic potential of a
circle); Duplantier–Sheffield, loc. cit.
-/

noncomputable section

namespace LatticeProb

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Average of `w ↦ log ‖w - z‖` over `∂B_r(0)`: the logarithmic mean value property, `log max(r, |z|)`
(Armitage–Gardiner, Section 3.1). -/
lemma circleAverage_log_norm_sub_eq {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) 0 r = Real.log (max r ‖z‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := (0 : ℂ)) (a := z) hr.ne'
  rw [h, zero_sub, norm_neg]
  rcases le_total ‖z‖ r with hz | hz
  · rw [max_eq_left hz]
    have hle : r⁻¹ * ‖z‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ hr, mul_one]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = 0 := by
      unfold Real.posLog
      exact max_eq_left (Real.log_nonpos (by positivity) hle)
    rw [hpos, add_zero]
  · rw [max_eq_right hz]
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hr hz
    have h1 : 1 ≤ r⁻¹ * ‖z‖ := by
      rw [inv_mul_eq_div, one_le_div hr]; exact hz
    have hpos : Real.posLog (r⁻¹ * ‖z‖) = Real.log (r⁻¹ * ‖z‖) := by
      unfold Real.posLog
      exact max_eq_right (Real.log_nonneg h1)
    rw [hpos, Real.log_mul (inv_ne_zero hr.ne') hz0.ne', Real.log_inv]
    ring

/-- The circle average of the covariance kernel `wholePlaneCov z ·` over `∂B_r(0)`, for every `z ∈ ℂ`
(Duplantier–Sheffield 2011, Section 3.1; the mean value property of `log |· - z|`). The point `w = z` of the
circle, where `wholePlaneCov` takes the junk value `0`, is a single point of the codiscrete filter and does not
contribute. -/
lemma circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r =
      Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log (max r ‖z‖) := by
  have hA : max ‖z‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hB : max r 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hgood : (Metric.sphere (0 : ℂ) |r| \ {z}) ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |r|) := by
    rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
    intro x _
    refine ⟨univ, univ_mem, (Set.finite_singleton z).subset ?_⟩
    rintro y ⟨-, hyS, hy⟩
    exact Set.mem_singleton_iff.mp (not_not.mp fun hne => hy ⟨hyS, hne⟩)
  have hcod : (fun w : ℂ => wholePlaneCov z w) =ᶠ[codiscreteWithin (Metric.sphere (0 : ℂ) |r|)]
      (fun w : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1) - Real.log ‖w - z‖) := by
    filter_upwards [hgood] with w hw
    obtain ⟨hwS, hwz⟩ := hw
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hwS
    have hwz' : ‖z - w‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact fun h => hwz (Set.mem_singleton_iff.mpr h.symm)
    unfold wholePlaneCov
    rw [hwS, Real.log_div (mul_ne_zero hA hB) hwz', Real.log_mul hA hB, norm_sub_rev]
  have h1 : CircleIntegrable (fun _ : ℂ => Real.log (max ‖z‖ 1) + Real.log (max r 1)) 0 r := by
    unfold CircleIntegrable
    exact intervalIntegrable_const
  have h2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) 0 r :=
    circleIntegrable_log_norm_sub_const (c := (0 : ℂ)) (a := z) r
  rw [Real.circleAverage_congr_codiscreteWithin hcod hr.ne']
  have key := Real.circleAverage_fun_sub h1 h2
  beta_reduce at key
  rw [key, Real.circleAverage_const, circleAverage_log_norm_sub_eq hr z]

/-- The circle-circle covariance of the whole-plane GFF: the circle average over `∂B_s(0)` of the circle averages
of `wholePlaneCov · ` over `∂B_r(0)`, for `s ≠ r` (Duplantier–Sheffield 2011, eq. (3.2)). -/
lemma circleAverage_circleAverage_wholePlaneCov {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Real.circleAverage (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r) 0 s =
      Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s) := by
  have hc : EqOn (fun z : ℂ => Real.circleAverage (fun w : ℂ => wholePlaneCov z w) 0 r)
      (fun _ : ℂ => Real.log (max s 1) + Real.log (max r 1) - Real.log (max r s))
      (Metric.sphere (0 : ℂ) |s|) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hs] at hz
    dsimp only
    rw [circleAverage_wholePlaneCov hr z, hz]
  rw [Real.circleAverage_congr_sphere hc, Real.circleAverage_const]

/-! ### Logarithmic integrability and the radial parameter -/

/-- For `0 < t ≤ R`, `|log t| ≤ 2 (1 + R) t^{-1/2}`: the logarithm is dominated by an integrable power at `0`. -/
lemma abs_log_le_rpow_neg_half {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    |Real.log t| ≤ 2 * (1 + R) * t ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hrp : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
  rw [hrp, abs_le]
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht.le]; ring
  have hup : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have hlo : Real.log (Real.sqrt t)⁻¹ ≤ (Real.sqrt t)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at hlo
  have hsR : Real.sqrt t ≤ R * (Real.sqrt t)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hs]
    nlinarith
  have hinv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hs
  constructor
  · nlinarith
  · nlinarith

/-- `x ↦ φ x * log ‖x‖` is integrable for a test function `φ` (logarithmic singularity at `0`). -/
lemma integrable_test_mul_log_norm {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => φ x * Real.log ‖x‖) := by
  obtain ⟨hc, hcs, -⟩ := hφ
  obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1 hcs.isCompact.isBounded
  obtain ⟨M, hM⟩ := hc.continuous.bounded_above_of_compact_support hcs
  have hsub : tsupport φ ⊆ ball (0 : ℂ) (R + 1) := hR.trans (closedBall_subset_ball (by linarith))
  have hsupp : Function.support (fun x : ℂ => φ x * Real.log ‖x‖) ⊆ ball (0 : ℂ) (R + 1) := by
    intro x hx
    apply hsub
    apply subset_tsupport
    intro h0
    apply hx
    simp [h0]
  have hd : 1 ≤ Module.finrank ℝ ℂ := by simp
  have hα : (1 / 2 : ℝ) < (Module.finrank ℝ ℂ : ℝ) := by simp; norm_num
  have hmeas : AEStronglyMeasurable (fun x : ℂ => φ x * Real.log ‖x‖) volume :=
    (hc.continuous.measurable.mul (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  have hdecay : ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) (R + 1))),
      ‖φ x * Real.log ‖x‖‖ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
    refine ae_of_all _ fun x => ?_
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · have : x = 0 := norm_eq_zero.1 h0
      subst this
      simp
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      by_cases hx : ‖x‖ ≤ R + 1
      · rw [norm_mul, Real.norm_eq_abs]
        have h1 := abs_log_le_rpow_neg_half hxpos hx
        have h2 : ‖φ x‖ ≤ M := hM x
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        have h3 : 0 ≤ ‖x‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        calc ‖φ x‖ * |Real.log ‖x‖| ≤ M * (2 * (1 + (R + 1)) * ‖x‖ ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul h2 h1 (abs_nonneg _) ((norm_nonneg _).trans h2)
          _ = (M * (2 * (1 + (R + 1)))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (by linarith [le_abs_self (R + 1)]) hM0) h3
      · have hout : x ∉ tsupport φ := fun hxt => hx (by
          have := hR hxt
          rw [mem_closedBall, dist_zero_right] at this
          linarith)
        have : φ x = 0 := image_eq_zero_of_notMem_tsupport hout
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        simp only [this, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hM0 (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  have hloc : IntegrableOn (fun x : ℂ => φ x * Real.log ‖x‖) (ball (0 : ℂ) (R + 1)) :=
    integrableOn_ball_of_norm_le_rpow hd hα hdecay hmeas
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hloc

/-- The diagonal circle-circle covariance `2 log max(|x|,1) - log |x|` is nonnegative. -/
lemma diag_nonneg (x : ℂ) : 0 ≤ 2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖ := by
  rcases le_total ‖x‖ 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    have : Real.log ‖x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) h
    linarith
  · rw [max_eq_left h]
    have : 0 ≤ Real.log ‖x‖ := Real.log_nonneg h
    linarith

/-- `|φ(x)| (2 log max(|x|,1) - log |x|)` is integrable for a test function `φ`. -/
lemma integrable_abs_test_mul_diag {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => |φ x| * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) := by
  have hcont : Continuous (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) := by
    refine hφ.1.continuous.mul (Continuous.log (continuous_norm.max continuous_const) fun x => ?_)
    exact (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h1 : Integrable (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) :=
    hcont.integrable_of_hasCompactSupport (hφ.2.1.mul_right)
  have h2 := (h1.const_mul 2).sub (integrable_test_mul_log_norm hφ)
  have h3 : Integrable (fun x : ℂ => φ x * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) :=
    h2.congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  refine (h3.abs).congr (ae_of_all _ fun x => ?_)
  simp only
  rw [abs_mul, abs_of_nonneg (diag_nonneg x)]

/-- The point `(max(|x|,·), 0)` of the circle-parameter space at which the measurable version is evaluated;
it equals `(|x|, 0)` for `x ≠ 0` (Bonanno's circle-average parametrisation, Duplantier–Sheffield 2011, Section 3.1). -/
def radialPoint (x : ℂ) : CircleParameter :=
  (⟨if x = 0 then 1 else ‖x‖, by
    split_ifs with h
    · norm_num
    · exact norm_pos_iff.2 h⟩, 0)

lemma measurable_radialPoint : Measurable radialPoint := by
  refine Measurable.prodMk ?_ measurable_const
  refine Measurable.subtype_mk ?_
  exact Measurable.ite (measurableSet_singleton (0 : ℂ)) measurable_const measurable_norm


/-! ### Normalized circle averages: covariances and moments -/

section Normalized

open LQGMetric ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The Green kernel `gffGreen` and `wholePlaneCov` agree off the diagonal (Duplantier–Sheffield 2011, eq. (3.2)). -/
lemma gffGreen_eq_wholePlaneCov {x y : ℂ} (hxy : x ≠ y) :
    LQGDimension.gffGreen x y = wholePlaneCov x y := by
  have h1 : 0 < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h3 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold LQGDimension.gffGreen wholePlaneCov
  rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
  ring

/-- The circle averages of `gffGreen` and of `wholePlaneCov` coincide: the two kernels differ at most on the
diagonal, which meets a circle in at most one point (Armitage–Gardiner, Section 3.1). -/
lemma circleAverage_gffGreen_eq_wholePlaneCov (x : ℂ) {s : ℝ} (hs : s ≠ 0) :
    Real.circleAverage (fun y => LQGDimension.gffGreen x y) 0 s =
      Real.circleAverage (fun y => wholePlaneCov x y) 0 s := by
  apply Real.circleAverage_congr_codiscreteWithin _ hs
  filter_upwards [(compl_singleton_mem_codiscreteWithin x :
    ({x}ᶜ : Set ℂ) ∈ codiscreteWithin (sphere (0 : ℂ) |s|))] with y hy
  exact gffGreen_eq_wholePlaneCov (Ne.symm hy)

/-- Covariance of the normalized circle averages at concentric circles (Duplantier–Sheffield 2011, eq. (3.2)):
`cov(h_r(0), h_s(0)) = log max(r,1) + log max(s,1) - log max(r,s)`. -/
lemma covariance_circleAvg_zero {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    covariance (fun ω => circleAvg (h ω) r 0) (fun ω => circleAvg (h ω) s 0) P =
      Real.log (max r 1) + Real.log (max s 1) - Real.log (max r s) := by
  obtain ⟨H, hG, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  have hin : ∀ x : ℂ, Real.circleAverage (fun y => LQGDimension.gffGreen x y) 0 s =
      Real.circleAverage (fun y => wholePlaneCov x y) 0 s :=
    fun x => circleAverage_gffGreen_eq_wholePlaneCov x hs.ne'
  rw [← CircleAvg.covariance_congr_ae (hHae r hr 0) (hHae s hs 0), hG.covariance_eq r hr s hs 0 0,
    LQGDimension.Osc37.gffCircleCov_eq_circleAverage]
  simp only [hin]
  rw [circleAverage_circleAverage_wholePlaneCov hs hr, max_comm s r]

/-- Circle averages of positive radius are square integrable (they are Gaussian observables). -/
lemma memLp_two_circleAvg {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (fun ω => circleAvg (h ω) r z) 2 P := by
  obtain ⟨H, hG, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  exact (hG.isGaussianProcess.hasGaussianLaw_eval (⟨r, hr⟩, z)).memLp_two.ae_eq (hHae r hr z)

/-- The mean of a normalized circle average vanishes. -/
lemma integral_circleAvg_zero {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {t : ℝ} (ht : 0 < t) :
    ∫ ω, circleAvg (h ω) t 0 ∂P = 0 := by
  obtain ⟨H, hG, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  rw [integral_congr_ae (hHae t ht 0).symm]
  exact hG.integral_eq_zero t ht 0

/-- Covariance of centred random variables is the mean of their product. -/
lemma covariance_eq_integral_of_mean_zero {X Y : Ω → ℝ} (hY : ∫ ω, Y ω ∂P = 0) (hYi : Integrable Y P)
    (hXY : Integrable (fun ω => X ω * Y ω) P) :
    covariance X Y P = ∫ ω, X ω * Y ω ∂P := by
  unfold covariance
  have hpt : ∀ ω, (X ω - ∫ ω, X ω ∂P) * (Y ω - ∫ ω, Y ω ∂P) =
      X ω * Y ω - (∫ ω, X ω ∂P) * Y ω := by
    intro ω
    rw [hY]
    ring
  simp_rw [hpt]
  rw [integral_sub hXY (hYi.const_mul _), integral_const_mul, hY, mul_zero, sub_zero]

/-- The second-order mixed moment of two normalized circle averages at concentric circles. -/
lemma integral_mul_circleAvg_zero [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    ∫ ω, circleAvg (h ω) r 0 * circleAvg (h ω) s 0 ∂P =
      Real.log (max r 1) + Real.log (max s 1) - Real.log (max r s) := by
  have hc := covariance_circleAvg_zero hh hr hs
  rw [covariance_eq_integral_of_mean_zero (integral_circleAvg_zero hh hs)
    ((memLp_two_circleAvg hh hs 0).integrable one_le_two)
    ((memLp_two_circleAvg hh hr 0).integrable_mul (memLp_two_circleAvg hh hs 0))] at hc
  exact hc

/-- A measurable continuous version of the normalized circle averages. The almost sure continuity of
`(r, z) ↦ h_r(z)` is the named hypothesis `hcont` (Duplantier–Sheffield 2011, Proposition 3.1). -/
lemma exists_ae_circle_version {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => circleAvg (h ω) p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∃ F : Ω → C(CircleParameter, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2 := by
  obtain ⟨F, hFm, -, hF⟩ := exists_measurable_continuous_circleAvg_version hh.1
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense CircleParameter
  refine ⟨F, hFm, ?_⟩
  have hD : ∀ᵐ ω ∂P, ∀ p ∈ D, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2 - circleAvg (h ω) 1 0 :=
    (ae_ball_iff hDc).2 fun p _ => hF p
  filter_upwards [hD, hcont, hh.2] with ω hω hcontω h0
  have hmap : Continuous (fun p : CircleParameter => ((p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hfun : Continuous (fun p : CircleParameter =>
      circleAvg (h ω) (p.1 : ℝ) p.2 - circleAvg (h ω) 1 0) :=
    (hcontω.comp_continuous hmap (fun p => ⟨p.1.2, mem_univ _⟩)).sub continuous_const
  have heq := Continuous.ext_on hDd (F ω).continuous hfun (fun p hp => hω p hp)
  intro p
  have hp := congrFun heq p
  simp only [h0, sub_zero] at hp
  exact hp

/-- Joint measurability of `(ω, p) ↦ F ω p` for a measurable random continuous function `F`. -/
lemma measurable_circleVersion_joint {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F) :
    Measurable (fun q : Ω × CircleParameter => F q.1 q.2) := by
  have hm : Measurable (Function.uncurry fun (p : CircleParameter) (ω : Ω) => F ω p) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => (F ω).continuous)
      (fun p => (continuous_eval_const p).measurable.comp hF)
  exact hm.comp measurable_swap

/-- Measurability in `ω` of the radial functional `ω ↦ ∫ φ(x) F(ω)(|x|,0) dx`. -/
lemma measurable_radialIntegral_version {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable fun ω => ∫ x, φ x * F ω (radialPoint x) := by
  have hjoint : Measurable (fun q : Ω × ℂ => φ q.2 * F q.1 (radialPoint q.2)) :=
    Measurable.mul (hφ.comp measurable_snd)
      ((measurable_circleVersion_joint hF).comp
        (measurable_fst.prodMk (measurable_radialPoint.comp measurable_snd)))
  exact (hjoint.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

lemma radialPoint_fst_of_ne {x : ℂ} (hx : x ≠ 0) : ((radialPoint x).1 : ℝ) = ‖x‖ := by
  simp [radialPoint, hx]

lemma radialPoint_snd (x : ℂ) : (radialPoint x).2 = 0 := rfl

/-- Almost surely, the radial integral of the circle averages is the radial integral of the measurable version. -/
lemma ae_radialIntegral_eq {h : Ω → DistC} {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2) (φ : ℂ → ℝ) :
    ∀ᵐ ω ∂P, ∫ x, φ x * circleAvg (h ω) ‖x‖ 0 = ∫ x, φ x * F ω (radialPoint x) := by
  filter_upwards [hFae] with ω hω
  apply integral_congr_ae
  have h0 : ∀ᵐ x : ℂ ∂(volume : Measure ℂ), x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with x hx
  congr 1
  rw [hω (radialPoint x), radialPoint_fst_of_ne hx, radialPoint_snd]

/-- Square integrability of the radial functional at every point of the circle parameter space. -/
lemma memLp_two_radialPoint {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2) (y : ℂ) :
    MemLp (fun ω => F ω (radialPoint y)) 2 P :=
  (memLp_two_circleAvg hh (radialPoint y).1.2 0).ae_eq (by
    filter_upwards [hFae] with ω hω
    exact (hω (radialPoint y)).symm)

/-- `E[F(ω)(|x|,0)²] = 2 log max(|x|,1) - log |x|` for `x ≠ 0`. -/
lemma integral_sq_radialPoint [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2) {x : ℂ} (hx : x ≠ 0) :
    ∫ ω, (F ω (radialPoint x)) ^ 2 ∂P = 2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖ := by
  have hs : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hcongr : (fun ω => (F ω (radialPoint x)) ^ 2) =ᵐ[P]
      fun ω => circleAvg (h ω) ‖x‖ 0 * circleAvg (h ω) ‖x‖ 0 := by
    filter_upwards [hFae] with ω hω
    rw [hω (radialPoint x), radialPoint_fst_of_ne hx, radialPoint_snd]
    ring
  rw [integral_congr_ae hcongr, integral_mul_circleAvg_zero hh hs hs, max_self]
  ring

/-- `E[F(ω)(|x|,0) F(ω)(|y|,0)] = log max(|x|,1) + log max(|y|,1) - log max(|x|,|y|)` for `x, y ≠ 0`. -/
lemma integral_radialPoint_mul [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P)
    {F : Ω → C(CircleParameter, ℝ)}
    (hFae : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = circleAvg (h ω) (p.1 : ℝ) p.2) {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∫ ω, F ω (radialPoint x) * F ω (radialPoint y) ∂P =
      Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖) := by
  have hcongr : (fun ω => F ω (radialPoint x) * F ω (radialPoint y)) =ᵐ[P]
      fun ω => circleAvg (h ω) ‖x‖ 0 * circleAvg (h ω) ‖y‖ 0 := by
    filter_upwards [hFae] with ω hω
    rw [hω (radialPoint x), hω (radialPoint y), radialPoint_fst_of_ne hx, radialPoint_fst_of_ne hy,
      radialPoint_snd, radialPoint_snd]
  rw [integral_congr_ae hcongr]
  exact integral_mul_circleAvg_zero hh (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)

end Normalized

end LatticeProb

end
#print axioms LatticeProb.gffGreen_eq_wholePlaneCov
#print axioms LatticeProb.circleAverage_gffGreen_eq_wholePlaneCov
#print axioms LatticeProb.covariance_circleAvg_zero
#print axioms LatticeProb.memLp_two_circleAvg
#print axioms LatticeProb.integral_circleAvg_zero
#print axioms LatticeProb.covariance_eq_integral_of_mean_zero
#print axioms LatticeProb.integral_mul_circleAvg_zero
#print axioms LatticeProb.exists_ae_circle_version
#print axioms LatticeProb.measurable_circleVersion_joint
#print axioms LatticeProb.measurable_radialIntegral_version
#print axioms LatticeProb.ae_radialIntegral_eq
#print axioms LatticeProb.memLp_two_radialPoint
#print axioms LatticeProb.integral_sq_radialPoint
#print axioms LatticeProb.integral_radialPoint_mul
