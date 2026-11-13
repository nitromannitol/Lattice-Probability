/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.SpectralDiff at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.SpectralGram
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! Radial cancellation for the difference of two normalized spectral densities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped FourierTransform

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd IsLFPPKernel)

private def densityDiff {d : ℕ} (κ κ' : Rd d → ℝ) (η : Rd d) : ℝ :=
  ‖𝓕 (fun x : Rd d => (κ x : ℂ)) η‖ ^ 2 -
    ‖𝓕 (fun x : Rd d => (κ' x : ℂ)) η‖ ^ 2

private theorem integral_densityDiff {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    (∫ η : Rd d, densityDiff κ κ' η) = 0 := by
  unfold densityDiff
  rw [integral_sub (integrable_fourier_kernel_norm_sq hκ)
    (integrable_fourier_kernel_norm_sq hκ'),
    integral_fourier_kernel_norm_sq hκ,
    integral_fourier_kernel_norm_sq hκ']
  norm_num

private theorem densityDiff_eq_of_norm_eq {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η η' : Rd d} (hη : ‖η‖ = ‖η'‖) :
    densityDiff κ κ' η = densityDiff κ κ' η' := by
  unfold densityDiff
  rw [ki_fourier_kernel_eq_of_norm_eq hκ hη,
    ki_fourier_kernel_eq_of_norm_eq hκ' hη]

private theorem radial_densityDiff_smul {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    (η y : Rd d) :
    densityDiff κ κ' (‖y‖ • η) = densityDiff κ κ' (‖η‖ • y) := by
  apply densityDiff_eq_of_norm_eq hκ hκ'
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  ring

private theorem integral_radial_densityDiff_zero {d : ℕ}
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η : Rd d} (hη : η ≠ 0) :
    (∫ y : Rd d, densityDiff κ κ' (‖y‖ • η)) = 0 := by
  have hrad : (fun y : Rd d => densityDiff κ κ' (‖y‖ • η)) =
      fun y => densityDiff κ κ' (‖η‖ • y) := by
    funext y
    exact radial_densityDiff_smul hκ hκ' η y
  rw [hrad]
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have h := Measure.integral_comp_smul (volume : Measure (Rd d))
    (densityDiff κ κ') ‖η‖
  rw [finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hn _)),
    integral_densityDiff hκ hκ'] at h
  simpa only [smul_zero] using h

private theorem integral_densityDiff_ray_zero {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η : Rd d} (hη : η ≠ 0) :
    (∫ t in Ioi (0 : ℝ), t ^ (d - 1) * densityDiff κ κ' (t • η)) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hp := integral_fun_norm_addHaar (volume : Measure (Rd d))
    (fun t : ℝ => densityDiff κ κ' (t • η))
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul] at hp
  rw [integral_radial_densityDiff_zero hκ hκ' hη] at hp
  have hball : 0 < (volume : Measure (Rd d)).real (ball 0 1) := by
    exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 zero_lt_one))
      measure_ball_lt_top.ne
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hcoef : (d : ℝ) * (volume : Measure (Rd d)).real (ball 0 1) ≠ 0 :=
    ne_of_gt (mul_pos hdpos hball)
  have hp' : ((d : ℝ) * (volume : Measure (Rd d)).real (ball 0 1)) *
      (∫ t in Ioi (0 : ℝ), t ^ (d - 1) * densityDiff κ κ' (t • η)) = 0 := by
    simpa only [mul_assoc] using hp.symm
  exact (mul_eq_zero.mp hp').resolve_left hcoef

theorem norm_specVec_sub_sq_eq {d : ℕ} (hd : 1 ≤ d)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (z w : Rd d) :
    ‖specVec κ a b z - specVec κ a b w‖ ^ 2 =
      ‖HigherDimLFPP.bandVec κ a b z - HigherDimLFPP.bandVec κ a b w‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [← real_inner_self_eq_norm_sq]
  rw [inner_specVec hd hκ ha hab z z,
    inner_specVec hd hκ ha hab z w,
    inner_specVec hd hκ ha hab w w]

/-- The increment half of KI-2 follows from KI-1 and the original band-vector bound. -/
theorem exists_specVec_diff_increment_bound {d : ℕ} (hd : 2 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    ∃ L : ℝ, 0 < L ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ z w : Rd d,
      ‖(specVec κ ε 1 z - specVec κ' ε 1 z) -
        (specVec κ ε 1 w - specVec κ' ε 1 w)‖ ^ 2 ≤
          L * ‖z - w‖ ^ 2 / ε ^ 2 := by
  obtain ⟨Lκ, hLκ0, hLκ⟩ := HigherDimLFPP.exists_norm_bandVec_sub_sq_le hκ
  obtain ⟨Lκ', hLκ'0, hLκ'⟩ := HigherDimLFPP.exists_norm_bandVec_sub_sq_le hκ'
  refine ⟨2 * (Lκ + Lκ') + 1, by positivity, ?_⟩
  intro ε hε z w
  have hε1 : ε ≤ 1 := hε.2.le
  have hd1 : 1 ≤ d := by omega
  have hκb := (norm_specVec_sub_sq_eq hd1 hκ hε.1 hε1 z w).trans_le
    (hLκ ε hε.1 1 z w)
  have hκ'b := (norm_specVec_sub_sq_eq hd1 hκ' hε.1 hε1 z w).trans_le
    (hLκ' ε hε.1 1 z w)
  have htri : ‖(specVec κ ε 1 z - specVec κ' ε 1 z) -
        (specVec κ ε 1 w - specVec κ' ε 1 w)‖ ≤
      ‖specVec κ ε 1 z - specVec κ ε 1 w‖ +
        ‖specVec κ' ε 1 z - specVec κ' ε 1 w‖ := by
    calc
      _ = ‖(specVec κ ε 1 z - specVec κ ε 1 w) -
          (specVec κ' ε 1 z - specVec κ' ε 1 w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hsq : ‖(specVec κ ε 1 z - specVec κ' ε 1 z) -
        (specVec κ ε 1 w - specVec κ' ε 1 w)‖ ^ 2 ≤
      2 * (‖specVec κ ε 1 z - specVec κ ε 1 w‖ ^ 2 +
        ‖specVec κ' ε 1 z - specVec κ' ε 1 w‖ ^ 2) := by
    nlinarith [sq_nonneg (‖specVec κ ε 1 z - specVec κ ε 1 w‖ -
      ‖specVec κ' ε 1 z - specVec κ' ε 1 w‖),
      norm_nonneg ((specVec κ ε 1 z - specVec κ' ε 1 z) -
        (specVec κ ε 1 w - specVec κ' ε 1 w)),
      norm_nonneg (specVec κ ε 1 z - specVec κ ε 1 w),
      norm_nonneg (specVec κ' ε 1 z - specVec κ' ε 1 w)]
  have hden : 0 ≤ ‖z - w‖ ^ 2 / ε ^ 2 := by positivity
  calc
    _ ≤ 2 * (‖specVec κ ε 1 z - specVec κ ε 1 w‖ ^ 2 +
        ‖specVec κ' ε 1 z - specVec κ' ε 1 w‖ ^ 2) := hsq
    _ ≤ 2 * (Lκ * ‖z - w‖ ^ 2 / ε ^ 2 +
        Lκ' * ‖z - w‖ ^ 2 / ε ^ 2) := by gcongr
    _ = 2 * (Lκ + Lκ') * (‖z - w‖ ^ 2 / ε ^ 2) := by ring
    _ ≤ (2 * (Lκ + Lκ') + 1) * (‖z - w‖ ^ 2 / ε ^ 2) := by nlinarith
    _ = _ := by ring

private theorem exists_densityDiff_decay_bound {d : ℕ}
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Rd d,
      ‖η‖ ^ (d + 2) * |densityDiff κ κ' η| ≤ C := by
  let F := 𝓕 (kiKernelSchwartz hκ)
  let F' := 𝓕 (kiKernelSchwartz hκ')
  let B := (SchwartzMap.seminorm ℂ 0 0 F) *
    (SchwartzMap.seminorm ℂ (d + 2) 0 F)
  let B' := (SchwartzMap.seminorm ℂ 0 0 F') *
    (SchwartzMap.seminorm ℂ (d + 2) 0 F')
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  refine ⟨B + B' + 1, by positivity, ?_⟩
  intro η
  have hF0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ F 0 η
  have hFk := SchwartzMap.norm_pow_mul_le_seminorm ℂ F (d + 2) η
  have hF'0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ F' 0 η
  have hF'k := SchwartzMap.norm_pow_mul_le_seminorm ℂ F' (d + 2) η
  simp only [pow_zero, one_mul] at hF0 hF'0
  have hF : ‖η‖ ^ (d + 2) * ‖F η‖ ^ 2 ≤ B := by
    calc
      _ = (‖η‖ ^ (d + 2) * ‖F η‖) * ‖F η‖ := by ring
      _ ≤ (SchwartzMap.seminorm ℂ (d + 2) 0 F) *
          (SchwartzMap.seminorm ℂ 0 0 F) :=
            mul_le_mul hFk hF0 (norm_nonneg _) (by positivity)
      _ = B := by dsimp [B]; ring
  have hF' : ‖η‖ ^ (d + 2) * ‖F' η‖ ^ 2 ≤ B' := by
    calc
      _ = (‖η‖ ^ (d + 2) * ‖F' η‖) * ‖F' η‖ := by ring
      _ ≤ (SchwartzMap.seminorm ℂ (d + 2) 0 F') *
          (SchwartzMap.seminorm ℂ 0 0 F') :=
            mul_le_mul hF'k hF'0 (norm_nonneg _) (by positivity)
      _ = B' := by dsimp [B']; ring
  have hFourier : (F η) = 𝓕 (fun x : Rd d => (κ x : ℂ)) η := by
    congr 1
  have hFourier' : (F' η) = 𝓕 (fun x : Rd d => (κ' x : ℂ)) η := by
    congr 1
  unfold densityDiff
  rw [← hFourier, ← hFourier']
  have habs : |‖F η‖ ^ 2 - ‖F' η‖ ^ 2| ≤ ‖F η‖ ^ 2 + ‖F' η‖ ^ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [sq_nonneg ‖F η‖, sq_nonneg ‖F' η‖]
  calc
    _ ≤ ‖η‖ ^ (d + 2) * (‖F η‖ ^ 2 + ‖F' η‖ ^ 2) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ B + B' := by nlinarith [hF, hF']
    _ ≤ B + B' + 1 := by linarith

private theorem continuous_densityDiff {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    Continuous (densityDiff κ κ') := by
  unfold densityDiff
  exact ((ki_continuous_fourier_kernel hκ).norm.pow 2).sub
    ((ki_continuous_fourier_kernel hκ').norm.pow 2)

private theorem continuous_rayIntegrand {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') (η : Rd d) :
    Continuous (fun t : ℝ => t ^ (d - 1) * densityDiff κ κ' (t • η)) := by
  exact (continuous_id.pow _).mul
    ((continuous_densityDiff hκ hκ').comp (continuous_id.smul continuous_const))

private def phiDiff {d : ℕ} (κ κ' : Rd d → ℝ) (η : Rd d) : ℝ :=
  bandSpec κ 0 1 η - bandSpec κ' 0 1 η

private theorem measurable_phiDiff {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    Measurable (phiDiff κ κ') :=
  (measurable_bandSpec hκ 0 1).sub (measurable_bandSpec hκ' 0 1)

private theorem phiDiff_eq_integral {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') (η : Rd d) :
    phiDiff κ κ' η =
      ∫ t in Ioo (0 : ℝ) 1, t ^ (d - 1) * densityDiff κ κ' (t • η) := by
  have hκi : IntegrableOn (fun t : ℝ => t ^ (d - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • η)‖ ^ 2) (Ioo 0 1) := by
    exact (((continuous_id.pow _).mul
      (((ki_continuous_fourier_kernel hκ).comp
        (continuous_id.smul continuous_const)).norm.pow 2)).continuousOn.integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
  have hκ'i : IntegrableOn (fun t : ℝ => t ^ (d - 1) *
      ‖𝓕 (fun x : Rd d => (κ' x : ℂ)) (t • η)‖ ^ 2) (Ioo 0 1) := by
    exact (((continuous_id.pow _).mul
      (((ki_continuous_fourier_kernel hκ').comp
        (continuous_id.smul continuous_const)).norm.pow 2)).continuousOn.integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
  unfold phiDiff bandSpec densityDiff
  rw [← integral_sub hκi hκ'i]
  congr 1
  funext t
  ring

private theorem integrableOn_ray_Ioo {d : ℕ} {κ κ' : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') (η : Rd d)
    {a b : ℝ} :
    IntegrableOn (fun t : ℝ => t ^ (d - 1) * densityDiff κ κ' (t • η))
      (Ioo a b) := by
  exact ((continuous_rayIntegrand hκ hκ' η).continuousOn.integrableOn_Icc).mono_set
    Ioo_subset_Icc_self

private theorem integrableOn_inv_cube_Ioi :
    IntegrableOn (fun t : ℝ => (t ^ 3)⁻¹) (Ioi 1) := by
  apply (integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    zero_lt_one).congr_fun _ measurableSet_Ioi
  intro t ht
  change t ^ (-3 : ℝ) = (t ^ 3)⁻¹
  rw [Real.rpow_neg (zero_lt_one.trans ht).le]
  norm_cast

private theorem ray_decay_bound {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} {C : ℝ}
    (hC : ∀ ν : Rd d, ‖ν‖ ^ (d + 2) * |densityDiff κ κ' ν| ≤ C)
    {η : Rd d} (hη : η ≠ 0) {t : ℝ} (ht : 1 < t) :
    t ^ (d - 1) * |densityDiff κ κ' (t • η)| ≤
      (C / ‖η‖ ^ (d + 2)) * (t ^ 3)⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hη0 : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hpow : t ^ (d - 1) * (‖η‖ ^ (d + 2) * t ^ 3) =
      (t * ‖η‖) ^ (d + 2) := by
    have hexp : d - 1 + 3 = d + 2 := by omega
    calc
      _ = t ^ (d - 1 + 3) * ‖η‖ ^ (d + 2) := by rw [pow_add]; ring
      _ = t ^ (d + 2) * ‖η‖ ^ (d + 2) := by rw [hexp]
      _ = _ := by rw [mul_pow]
  have hdec := hC (t • η)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hdec
  have hR : 0 < ‖η‖ ^ (d + 2) := pow_pos hη0 _
  have ht3 : 0 < t ^ 3 := pow_pos ht0 _
  have hbound : t ^ (d - 1) * |densityDiff κ κ' (t • η)| ≤
      C / (‖η‖ ^ (d + 2) * t ^ 3) := by
    apply (le_div_iff₀ (mul_pos hR ht3)).2
    calc
      _ = (t * ‖η‖) ^ (d + 2) * |densityDiff κ κ' (t • η)| := by rw [← hpow]; ring
      _ ≤ C := hdec
  calc
    _ ≤ C / (‖η‖ ^ (d + 2) * t ^ 3) := hbound
    _ = (C / ‖η‖ ^ (d + 2)) * (t ^ 3)⁻¹ := by
      field_simp [hR.ne', ht3.ne']

private theorem integrableOn_ray_Ioi {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η : Rd d} (hη : η ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (d - 1) * densityDiff κ κ' (t • η))
      (Ioi 1) := by
  obtain ⟨C, _hCpos, hC⟩ := exists_densityDiff_decay_bound hκ hκ'
  have hη0 : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hmaj := integrableOn_inv_cube_Ioi.const_mul
    (C / ‖η‖ ^ (d + 2))
  apply hmaj.mono' (continuous_rayIntegrand hκ hκ' η).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (zero_lt_one.trans ht).le _)]
  exact ray_decay_bound hd hC hη ht

private theorem integrableOn_ray_Ioi_zero {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η : Rd d} (hη : η ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (d - 1) * densityDiff κ κ' (t • η))
      (Ioi 0) := by
  have hlocal := integrableOn_ray_Ioo hκ hκ' η (a := 0) (b := 1)
  have htail := integrableOn_ray_Ioi hd hκ hκ' hη
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hlocal).union htail

private theorem phiDiff_eq_neg_tail {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {η : Rd d} (hη : η ≠ 0) :
    phiDiff κ κ' η =
      -(∫ t in Ioi (1 : ℝ), t ^ (d - 1) * densityDiff κ κ' (t • η)) := by
  let f : ℝ → ℝ := fun t => t ^ (d - 1) * densityDiff κ κ' (t • η)
  have hzero := integral_densityDiff_ray_zero hd hκ hκ' hη
  change (∫ t in Ioi (0 : ℝ), f t) = 0 at hzero
  have hIoi := integrableOn_ray_Ioi_zero hd hκ hκ' hη
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hIoi
    (by norm_num : (0 : ℝ) ≤ 1)
  change (∫ t in Ioi (0 : ℝ), f t) - (∫ t in Ioi (1 : ℝ), f t) =
    ∫ t in (0 : ℝ)..1, f t at hsplit
  rw [hzero, zero_sub, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo] at hsplit
  rw [phiDiff_eq_integral hκ hκ' η]
  exact hsplit.symm

private theorem integral_inv_cube_Ioi :
    (∫ t in Ioi (1 : ℝ), (t ^ 3)⁻¹) = 1 / 2 := by
  have h := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) zero_lt_one
  have heq : (∫ t in Ioi (1 : ℝ), (t ^ 3)⁻¹) =
      ∫ t in Ioi (1 : ℝ), t ^ (-3 : ℝ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_neg (zero_lt_one.trans ht).le]
    norm_cast
  rw [heq, h]
  norm_num

private theorem phiDiff_far_bound {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {C : ℝ} (hC : ∀ ν : Rd d,
      ‖ν‖ ^ (d + 2) * |densityDiff κ κ' ν| ≤ C)
    {η : Rd d} (hη : η ≠ 0) :
    |phiDiff κ κ' η| ≤ C / (2 * ‖η‖ ^ (d + 2)) := by
  have htail := integrableOn_ray_Ioi hd hκ hκ' hη
  have hη0 : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hmaj := integrableOn_inv_cube_Ioi.const_mul
    (C / ‖η‖ ^ (d + 2))
  rw [phiDiff_eq_neg_tail hd hκ hκ' hη, abs_neg]
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ),
        |t ^ (d - 1) * densityDiff κ κ' (t • η)| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi (1 : ℝ),
        (C / ‖η‖ ^ (d + 2)) * (t ^ 3)⁻¹ := by
      apply integral_mono_ae htail.abs hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change |t ^ (d - 1) * densityDiff κ κ' (t • η)| ≤
        (C / ‖η‖ ^ (d + 2)) * (t ^ 3)⁻¹
      rw [abs_mul, abs_of_nonneg (pow_nonneg (zero_lt_one.trans ht).le _)]
      exact ray_decay_bound hd hC hη ht
    _ = (C / ‖η‖ ^ (d + 2)) * (1 / 2) := by
      rw [integral_const_mul, integral_inv_cube_Ioi]
    _ = C / (2 * ‖η‖ ^ (d + 2)) := by ring

private theorem exists_densityDiff_uniform_bound {d : ℕ}
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    ∃ M : ℝ, 0 < M ∧ ∀ η : Rd d, |densityDiff κ κ' η| ≤ M := by
  let F := 𝓕 (kiKernelSchwartz hκ)
  let F' := 𝓕 (kiKernelSchwartz hκ')
  let B := SchwartzMap.seminorm ℂ 0 0 F
  let B' := SchwartzMap.seminorm ℂ 0 0 F'
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  refine ⟨B ^ 2 + B' ^ 2 + 1, by positivity, ?_⟩
  intro η
  have hF := SchwartzMap.norm_le_seminorm ℂ F η
  have hF' := SchwartzMap.norm_le_seminorm ℂ F' η
  have hFourier : (F η) = 𝓕 (fun x : Rd d => (κ x : ℂ)) η := by congr 1
  have hFourier' : (F' η) = 𝓕 (fun x : Rd d => (κ' x : ℂ)) η := by congr 1
  unfold densityDiff
  rw [← hFourier, ← hFourier']
  have habs : |‖F η‖ ^ 2 - ‖F' η‖ ^ 2| ≤ ‖F η‖ ^ 2 + ‖F' η‖ ^ 2 := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [sq_nonneg ‖F η‖, sq_nonneg ‖F' η‖]
  nlinarith [sq_nonneg (B - ‖F η‖), sq_nonneg (B' - ‖F' η‖),
    norm_nonneg (F η), norm_nonneg (F' η)]

private theorem phiDiff_uniform_bound {d : ℕ}
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {M : ℝ} (hM : ∀ ν : Rd d, |densityDiff κ κ' ν| ≤ M)
    (η : Rd d) : |phiDiff κ κ' η| ≤ M := by
  have hlocal := integrableOn_ray_Ioo hκ hκ' η (a := 0) (b := 1)
  rw [phiDiff_eq_integral hκ hκ' η]
  calc
    _ ≤ ∫ t in Ioo (0 : ℝ) 1,
        |t ^ (d - 1) * densityDiff κ κ' (t • η)| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioo (0 : ℝ) 1, (M : ℝ) := by
      have hconst : Integrable (fun _ : ℝ => M) (volume.restrict (Ioo 0 1)) :=
        integrableOn_const measure_Ioo_lt_top.ne
      apply integral_mono_ae hlocal.abs hconst
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      change |t ^ (d - 1) * densityDiff κ κ' (t • η)| ≤ M
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1.le _)]
      calc
        _ ≤ t ^ (d - 1) * M := mul_le_mul_of_nonneg_left (hM (t • η)) (pow_nonneg ht.1.le _)
        _ ≤ M := by
          have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (t • η))
          exact mul_le_of_le_one_left hM0 (pow_le_one₀ ht.1.le ht.2.le)
    _ = M := by norm_num

private theorem integrable_inv_norm_pow_outside {d : ℕ} (hd : 1 ≤ d) :
    Integrable (fun η : Rd d =>
      (closedBall (0 : Rd d) 1)ᶜ.indicator
        (fun η => (‖η‖ ^ (d + 2))⁻¹) η) volume := by
  haveI : NeZero d := ⟨by omega⟩
  let f : ℝ → ℝ := fun s => (Ioi (1 : ℝ)).indicator
    (fun s => (s ^ (d + 2))⁻¹) s
  have hrad : Integrable (fun η : Rd d => f ‖η‖) volume := by
    apply (integrable_fun_norm_addHaar (volume : Measure (Rd d))).2
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    change IntegrableOn (fun s : ℝ => s ^ (d - 1) * f s) (Ioi 0)
    have hbase : Integrable (fun s : ℝ =>
        (Ioi (1 : ℝ)).indicator (fun s => (s ^ 3)⁻¹) s) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2 integrableOn_inv_cube_Ioi
    have heq : (fun s : ℝ => s ^ (d - 1) * f s) =
        fun s => (Ioi (1 : ℝ)).indicator (fun s => (s ^ 3)⁻¹) s := by
      funext s
      by_cases hs : s ∈ Ioi (1 : ℝ)
      · have hs0 : 0 < s := zero_lt_one.trans hs
        simp only [f, indicator_of_mem hs]
        have hexp : d - 1 + 3 = d + 2 := by omega
        have hpow : s ^ (d - 1) * s ^ 3 = s ^ (d + 2) := by
          rw [← pow_add, hexp]
        field_simp [ne_of_gt (pow_pos hs0 (d + 2)), ne_of_gt (pow_pos hs0 3)]
        nlinarith [hpow]
      · simp [f, hs]
    rw [heq]
    exact hbase.integrableOn
  apply hrad.congr
  filter_upwards [] with η
  by_cases h : 1 < ‖η‖
  · have hmem : η ∈ (closedBall (0 : Rd d) 1)ᶜ := by simpa using h
    simp [f, h, hmem]
  · have hnot : η ∉ (closedBall (0 : Rd d) 1)ᶜ := by simpa using h
    simp [f, h, hnot]

private theorem integrable_phiDiff {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    Integrable (phiDiff κ κ') volume := by
  obtain ⟨M, _hMpos, hM⟩ := exists_densityDiff_uniform_bound hκ hκ'
  obtain ⟨C, _hCpos, hC⟩ := exists_densityDiff_decay_bound hκ hκ'
  let B : Set (Rd d) := closedBall 0 1
  have hmeas : AEStronglyMeasurable (phiDiff κ κ') volume :=
    (measurable_phiDiff hκ hκ').aestronglyMeasurable
  have hinside : IntegrableOn (phiDiff κ κ') B := by
    have hconst : Integrable (fun _ : Rd d => M) (volume.restrict B) :=
      integrableOn_const measure_closedBall_lt_top.ne
    apply hconst.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with η hη
    rw [Real.norm_eq_abs]
    exact phiDiff_uniform_bound hκ hκ' hM η
  have houtside : IntegrableOn (phiDiff κ κ') Bᶜ := by
    have hmaj : IntegrableOn (fun η : Rd d => (C / 2) *
        (closedBall (0 : Rd d) 1)ᶜ.indicator
          (fun η => (‖η‖ ^ (d + 2))⁻¹) η) Bᶜ :=
      ((integrable_inv_norm_pow_outside hd).const_mul (C / 2)).integrableOn
    apply hmaj.mono' hmeas.restrict
    filter_upwards [ae_restrict_mem (measurableSet_closedBall.compl)] with η hη
    have hηnorm : 1 < ‖η‖ := by simpa [B] using hη
    have hη0 : η ≠ 0 := by
      intro heq
      simp [heq] at hηnorm
      linarith
    have hmem : η ∈ (closedBall (0 : Rd d) 1)ᶜ := by simpa [B] using hη
    rw [Real.norm_eq_abs]
    have hbound := phiDiff_far_bound hd hκ hκ' hC hη0
    rw [indicator_of_mem hmem]
    convert hbound using 1; ring
  have h := hinside.union houtside
  simpa only [union_compl_self, integrableOn_univ] using h

private theorem integral_ray_zero_eps {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (η : Rd d) :
    (∫ t in Ioo (0 : ℝ) ε, t ^ (d - 1) * densityDiff κ κ' (t • η)) =
      ε ^ d * phiDiff κ κ' (ε • η) := by
  let f : ℝ → ℝ := fun t => t ^ (d - 1) * densityDiff κ κ' (t • η)
  have hcomp := intervalIntegral.smul_integral_comp_mul_left
    (a := 0) (b := 1) f ε
  simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
  have hmul : ∀ s : ℝ, ε * f (ε * s) =
      ε ^ d * (s ^ (d - 1) * densityDiff κ κ' (s • (ε • η))) := by
    intro s
    have hp : ε ^ d = ε ^ (d - 1) * ε := by
      calc
        ε ^ d = ε ^ (d - 1 + 1) := by rw [Nat.sub_add_cancel hd]
        _ = ε ^ (d - 1) * ε := by rw [pow_add, pow_one]
    dsimp [f]
    rw [mul_pow, smul_smul]
    rw [hp]
    ring_nf
  have hform : (∫ t in (0 : ℝ)..ε, f t) =
      ε ^ d * ∫ s in (0 : ℝ)..1,
        s ^ (d - 1) * densityDiff κ κ' (s • (ε • η)) := by
    rw [← hcomp, ← intervalIntegral.integral_const_mul]
    simp_rw [hmul]
    rw [intervalIntegral.integral_const_mul]
  have hphi := phiDiff_eq_integral hκ hκ' (ε • η)
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hphi
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hε.le]
  exact hform.trans (by rw [← hphi])

private theorem bandSpec_diff_eq_phiDiff {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (η : Rd d) :
    bandSpec κ ε 1 η - bandSpec κ' ε 1 η =
      phiDiff κ κ' η - ε ^ d * phiDiff κ κ' (ε • η) := by
  let f : ℝ → ℝ := fun t => t ^ (d - 1) * densityDiff κ κ' (t • η)
  have hcont := continuous_rayIntegrand hκ hκ' η
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 ε)
    (hcont.intervalIntegrable (μ := volume) ε 1)
  have hband : bandSpec κ ε 1 η - bandSpec κ' ε 1 η =
      ∫ t in ε..1, f t := by
    unfold bandSpec
    simp_rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hε1]
    rw [← intervalIntegral.integral_sub]
    · congr 1
      funext t
      dsimp [f, densityDiff]
      ring
    · exact ((continuous_id.pow _).mul
        (((ki_continuous_fourier_kernel hκ).comp
          (continuous_id.smul continuous_const)).norm.pow 2)).intervalIntegrable
            (μ := volume) ε 1
    · exact ((continuous_id.pow _).mul
        (((ki_continuous_fourier_kernel hκ').comp
          (continuous_id.smul continuous_const)).norm.pow 2)).intervalIntegrable
            (μ := volume) ε 1
  have hphi := phiDiff_eq_integral hκ hκ' η
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hphi
  have hsmall := integral_ray_zero_eps hd hκ hκ' hε η
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hε.le] at hsmall
  rw [hsmall, ← hphi] at hsplit
  rw [hband]
  linarith

private theorem integrable_bandSpec_diff {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun η : Rd d => bandSpec κ ε 1 η - bandSpec κ' ε 1 η) volume := by
  have hphi := integrable_phiDiff hd hκ hκ'
  have hscale := (hphi.comp_smul hε.ne').const_mul (ε ^ d)
  have h := hphi.sub hscale
  apply h.congr
  filter_upwards [] with η
  exact (bandSpec_diff_eq_phiDiff hd hκ hκ' hε hε1 η).symm

private theorem integral_abs_bandSpec_diff_le {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ η : Rd d, |bandSpec κ ε 1 η - bandSpec κ' ε 1 η|) ≤
      2 * ∫ η : Rd d, |phiDiff κ κ' η| := by
  have hphi := (integrable_phiDiff hd hκ hκ').abs
  have hscale := (hphi.comp_smul hε.ne').const_mul (ε ^ d)
  have hdiff := (integrable_bandSpec_diff hd hκ hκ' hε hε1).abs
  have hchange := Measure.integral_comp_smul (volume : Measure (Rd d))
    (fun η : Rd d => |phiDiff κ κ' η|) ε
  rw [finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hε _))] at hchange
  simp only [smul_eq_mul] at hchange
  have hmass : (∫ η : Rd d, ε ^ d * |phiDiff κ κ' (ε • η)|) =
      ∫ η : Rd d, |phiDiff κ κ' η| := by
    rw [integral_const_mul, hchange]
    field_simp [ne_of_gt (pow_pos hε d)]
  have hbound : ∀ η : Rd d,
      |bandSpec κ ε 1 η - bandSpec κ' ε 1 η| ≤
        |phiDiff κ κ' η| + ε ^ d * |phiDiff κ κ' (ε • η)| := by
    intro η
    rw [bandSpec_diff_eq_phiDiff hd hκ hκ' hε hε1 η]
    calc
      _ = |phiDiff κ κ' η + -(ε ^ d * phiDiff κ κ' (ε • η))| := by
        rw [sub_eq_add_neg]
      _ ≤ |phiDiff κ κ' η| + |-(ε ^ d * phiDiff κ κ' (ε • η))| :=
        abs_add_le _ _
      _ = _ := by simp only [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hε.le _)]
  have hint := integral_mono hdiff (hphi.add hscale) hbound
  simp only [Pi.add_apply] at hint
  rw [integral_add hphi hscale, hmass] at hint
  linarith

private theorem sqrt_sub_sq_le_abs_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ |x - y| := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hnx := Real.sqrt_nonneg x
  have hny := Real.sqrt_nonneg y
  rcases le_total x y with hxy | hyx
  · have hsqrt := Real.sqrt_le_sqrt hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    nlinarith [mul_nonneg hnx (sub_nonneg.mpr hsqrt)]
  · have hsqrt := Real.sqrt_le_sqrt hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    nlinarith [mul_nonneg hny (sub_nonneg.mpr hsqrt)]

private def specDiffMajorant {d : ℕ} (κ κ' : Rd d → ℝ) (ε : ℝ)
    (p : ℝ × Rd d) : ℝ :=
  (Ico (0 : ℝ) 2).indicator
    (fun _ => |bandSpec κ ε 1 p.2 - bandSpec κ' ε 1 p.2|) p.1

private theorem specFun_diff_sq_le {d : ℕ} (κ κ' : Rd d → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (z : Rd d) (p : ℝ × Rd d) :
    (specFun κ ε 1 z p - specFun κ' ε 1 z p) ^ 2 ≤
      specDiffMajorant κ κ' ε p := by
  let S := bandSpec κ ε 1 p.2
  let S' := bandSpec κ' ε 1 p.2
  have hS : 0 ≤ S := bandSpec_nonneg κ hε p.2
  have hS' : 0 ≤ S' := bandSpec_nonneg κ' hε p.2
  have hroot := sqrt_sub_sq_le_abs_sub hS hS'
  by_cases h0 : p.1 ∈ Ico (0 : ℝ) 1
  · have h1 : p.1 ∉ Ico (1 : ℝ) 2 := by
      intro h1
      exact (not_lt_of_ge h1.1) h0.2
    have h2 : p.1 ∈ Ico (0 : ℝ) 2 := ⟨h0.1, h0.2.trans (by norm_num)⟩
    simp only [specFun, specDiffMajorant, indicator_of_mem h0,
      indicator_of_notMem h1, indicator_of_mem h2, add_zero]
    have hfactor : (Real.sqrt S * Real.cos (2 * Real.pi * inner ℝ z p.2) -
        Real.sqrt S' * Real.cos (2 * Real.pi * inner ℝ z p.2)) ^ 2 =
        (Real.sqrt S - Real.sqrt S') ^ 2 *
          Real.cos (2 * Real.pi * inner ℝ z p.2) ^ 2 := by ring
    rw [hfactor]
    calc
      _ ≤ |S - S'| * Real.cos (2 * Real.pi * inner ℝ z p.2) ^ 2 :=
        mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
      _ ≤ |S - S'| := by
        nlinarith [Real.cos_sq_le_one (2 * Real.pi * inner ℝ z p.2),
          abs_nonneg (S - S')]
  · by_cases h1 : p.1 ∈ Ico (1 : ℝ) 2
    · have h2 : p.1 ∈ Ico (0 : ℝ) 2 := ⟨(by linarith [h1.1]), h1.2⟩
      simp only [specFun, specDiffMajorant, indicator_of_notMem h0,
        indicator_of_mem h1, indicator_of_mem h2, zero_add]
      have hfactor : (Real.sqrt S * Real.sin (2 * Real.pi * inner ℝ z p.2) -
          Real.sqrt S' * Real.sin (2 * Real.pi * inner ℝ z p.2)) ^ 2 =
          (Real.sqrt S - Real.sqrt S') ^ 2 *
            Real.sin (2 * Real.pi * inner ℝ z p.2) ^ 2 := by ring
      rw [hfactor]
      calc
        _ ≤ |S - S'| * Real.sin (2 * Real.pi * inner ℝ z p.2) ^ 2 :=
          mul_le_mul_of_nonneg_right hroot (sq_nonneg _)
        _ ≤ |S - S'| := by
          nlinarith [Real.sin_sq_le_one (2 * Real.pi * inner ℝ z p.2),
            abs_nonneg (S - S')]
    · have h2 : p.1 ∉ Ico (0 : ℝ) 2 := by
        intro h2
        by_cases hp : p.1 < 1
        · exact h0 ⟨h2.1, hp⟩
        · exact h1 ⟨le_of_not_gt hp, h2.2⟩
      simp [specFun, specDiffMajorant, h0, h1, h2]

private theorem integrable_specDiffMajorant {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (specDiffMajorant κ κ' ε) volume := by
  have hI : Integrable ((Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)
  have hS := (integrable_bandSpec_diff hd hκ hκ' hε hε1).abs
  have hp := hI.mul_prod hS
  have heq : (fun p : ℝ × Rd d => specDiffMajorant κ κ' ε p) =
      fun p => (Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.1 *
        |bandSpec κ ε 1 p.2 - bandSpec κ' ε 1 p.2| := by
    funext p
    by_cases h : p.1 ∈ Ico (0 : ℝ) 2 <;> simp [specDiffMajorant, h]
  change Integrable (fun p : ℝ × Rd d => specDiffMajorant κ κ' ε p)
    (volume.prod volume)
  rw [heq]
  exact hp

private theorem integral_specDiffMajorant {d : ℕ} (κ κ' : Rd d → ℝ)
    (ε : ℝ) :
    (∫ p : ℝ × Rd d, specDiffMajorant κ κ' ε p) =
      2 * ∫ η : Rd d, |bandSpec κ ε 1 η - bandSpec κ' ε 1 η| := by
  have heq : (fun p : ℝ × Rd d => specDiffMajorant κ κ' ε p) =
      fun p => (Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℝ)) p.1 *
        |bandSpec κ ε 1 p.2 - bandSpec κ' ε 1 p.2| := by
    funext p
    by_cases h : p.1 ∈ Ico (0 : ℝ) 2 <;> simp [specDiffMajorant, h]
  rw [heq, show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl]
  rw [integral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Rd d)))
    ((Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℝ)))
    (fun η : Rd d => |bandSpec κ ε 1 η - bandSpec κ' ε 1 η|)]
  have hv : (volume.restrict (Ico (0 : ℝ) 2)).real univ = 2 := by norm_num
  simp only [integral_indicator measurableSet_Ico, integral_const, hv,
    smul_eq_mul, mul_one]

private theorem norm_specVec_diff_sq_eq_integral {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Rd d) :
    ‖specVec κ ε 1 z - specVec κ' ε 1 z‖ ^ 2 =
      ∫ p : ℝ × Rd d,
        (specFun κ ε 1 z p - specFun κ' ε 1 z p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (specVec κ ε 1 z) (specVec κ' ε 1 z),
    coeFn_specVec hd hκ hε hε1 z,
    coeFn_specVec hd hκ' hε hε1 z] with p hsub h1 h2
  rw [hsub, Pi.sub_apply, h1, h2]
  simp

private theorem norm_specVec_diff_sq_le {d : ℕ} (hd : 1 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ')
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Rd d) :
    ‖specVec κ ε 1 z - specVec κ' ε 1 z‖ ^ 2 ≤
      2 * ∫ η : Rd d, |bandSpec κ ε 1 η - bandSpec κ' ε 1 η| := by
  rw [norm_specVec_diff_sq_eq_integral hd hκ hκ' hε hε1 z]
  have hmem := (memLp_specFun hd hκ hε hε1 z).sub
    (memLp_specFun hd hκ' hε hε1 z)
  have hint : Integrable (fun p : ℝ × Rd d =>
      (specFun κ ε 1 z p - specFun κ' ε 1 z p) ^ 2) volume := by
    have h := hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using h
  exact (integral_mono hint (integrable_specDiffMajorant hd hκ hκ' hε hε1)
    (specFun_diff_sq_le κ κ' hε.le z)).trans_eq
      (integral_specDiffMajorant κ κ' ε)

/-- **KI-2.** Spectral kernel differences have uniformly bounded variance and LFPP-scale increments. -/
theorem exists_specVec_sub_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ κ' : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hκ' : IsLFPPKernel κ') :
    ∃ V L : ℝ, 0 < V ∧ 0 < L ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ z w : Rd d,
      ‖specVec κ ε 1 z - specVec κ' ε 1 z‖ ^ 2 ≤ V ∧
      ‖(specVec κ ε 1 z - specVec κ' ε 1 z) -
        (specVec κ ε 1 w - specVec κ' ε 1 w)‖ ^ 2 ≤
          L * ‖z - w‖ ^ 2 / ε ^ 2 := by
  obtain ⟨L, hLpos, hL⟩ := exists_specVec_diff_increment_bound hd hκ hκ'
  let M := ∫ η : Rd d, |phiDiff κ κ' η|
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  refine ⟨4 * M + 1, L, by positivity, hLpos, ?_⟩
  intro ε hε z w
  have hd1 : 1 ≤ d := by omega
  have hS := integral_abs_bandSpec_diff_le hd1 hκ hκ' hε.1 hε.2.le
  have hnorm := norm_specVec_diff_sq_le hd1 hκ hκ' hε.1 hε.2.le z
  constructor
  · dsimp [M] at hS ⊢
    linarith
  · exact hL ε hε z w

end HigherDimLQGMetric
