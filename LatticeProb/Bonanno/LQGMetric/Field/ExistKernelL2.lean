/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistKernelL2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `L²` bound for the white-noise kernels of the antiderivative field (task P2-EXIST, part 2)

`BddSupp.memLp_kerFun`: for bounded measurable `g` vanishing outside a ball, `kerFun g ∈ L²(ℝ × ℂ)`
with `‖kerFun g‖² ≤ π ∫ g² + (∫ |g|)(∫ |g(u)| ‖u‖²)/2`. Small times (`t ≤ 1`): Cauchy–Schwarz
against the probability density `p_{t/2}(·, y)`; large times: Cauchy–Schwarz against `|g|` and
`∫ (p_s(u,·) − p_s(0,·))² = 2(p_{2s}(0,0) − p_{2s}(u,0)) ≤ ‖u‖²/(8πs²)` (Tonelli throughout).
Own elementary proof (standard estimates).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric

namespace LQGMetric
namespace GFFExist

open WhiteNoise

variable {g : ℂ → ℝ} {M R : ℝ}

/-! ### The `L²` bound -/

lemma ofReal_integral_le_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

lemma lintegral_ofReal_heatKernel {s : ℝ} (hs : 0 < s) (u : ℂ) :
    ∫⁻ y, ENNReal.ofReal (heatKernel s u y) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel s hs u)
    (Eventually.of_forall fun y => heatKernel_nonneg s hs.le u y), integral_heatKernel s hs u,
    ENNReal.ofReal_one]

lemma lintegral_ofReal_sq_heatKernel_sub_le {s : ℝ} (hs : 0 < s) (u : ℂ) :
    ∫⁻ y, ENNReal.ofReal ((heatKernel s u y - heatKernel s 0 y) ^ 2) ≤
      ENNReal.ofReal (‖u‖ ^ 2 / (8 * Real.pi * s ^ 2)) := by
  have hi : Integrable fun y => (heatKernel s u y - heatKernel s 0 y) ^ 2 := by
    have e : (fun y => (heatKernel s u y - heatKernel s 0 y) ^ 2) = fun y =>
        heatKernel s u y * heatKernel s u y - 2 * (heatKernel s u y * heatKernel s 0 y) +
          heatKernel s 0 y * heatKernel s 0 y := by funext y; ring
    rw [e]
    exact ((integrable_heatKernel_mul_heatKernel s hs u u).sub
      ((integrable_heatKernel_mul_heatKernel s hs u 0).const_mul _)).add
      (integrable_heatKernel_mul_heatKernel s hs 0 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (integral_sq_heatKernel_sub_le s hs u)


/-- standing hypotheses on `g`: measurable, bounded by `M`, vanishing outside `B̄_R(0)` -/
structure BddSupp (g : ℂ → ℝ) (M R : ℝ) : Prop where
  meas : Measurable g
  bdd : ∀ u, |g u| ≤ M
  supp : ∀ u, R < ‖u‖ → g u = 0

lemma BddSupp.integrable_mul_bdd (hg : BddSupp g M R) {f : ℂ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ u, ‖u‖ ≤ R → |f u| ≤ K) : Integrable fun u => f u * g u := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg.bdd 0)
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (s := closedBall (0 : ℂ) R) (C := K * M) measure_closedBall_lt_top.ne))
    (hf.mul hg.meas).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hu, Real.norm_eq_abs, abs_mul]
    have hu' : ‖u‖ ≤ R := by simpa using hu
    exact mul_le_mul (hK u hu') (hg.bdd u) (abs_nonneg _) ((abs_nonneg _).trans (hK u hu'))
  · have hu' : R < ‖u‖ := by simpa using hu
    rw [indicator_of_notMem hu, hg.supp u hu', mul_zero, norm_zero]

lemma BddSupp.integrable (hg : BddSupp g M R) : Integrable g := by
  simpa using hg.integrable_mul_bdd (f := fun _ => 1) measurable_const (K := 1) (fun _ _ => by simp)

/-- the bound on the `y`-integral of `kerFun g (t, ·)²` -/
def slicBound (g : ℂ → ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => Real.pi * ∫ u, g u ^ 2) t +
    (Ioi (1 : ℝ)).indicator
      (fun t => (∫ u, |g u|) * (∫ u, |g u| * ‖u‖ ^ 2) / 2 * t ^ (-2 : ℝ)) t

lemma lintegral_kerFun_slice_le (hg : BddSupp g M R) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (kerFun g (t, y) ^ 2) ≤ ENNReal.ofReal (slicBound g t) := by
  have hgi := hg.integrable
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rcases le_or_gt t 0 with ht0 | ht0
  · simp [kerFun, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht0)]
  have hF : ∀ y, kerFun g (t, y) ^ 2 = Real.pi * kerInner g t y ^ 2 := fun y => by
    simp only [kerFun, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht0)]
    rw [mul_pow, hpi]
  simp_rw [hF]
  have hs : 0 < t / 2 := by linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · -- small times
    have hsl : slicBound g t = Real.pi * ∫ u, g u ^ 2 := by
      simp [slicBound, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht1)]
    rw [hsl]
    have hg2 : Integrable fun u => g u ^ 2 := by
      simpa [sq] using hg.integrable_mul_bdd hg.meas (K := M) (fun u _ => hg.bdd u)
    calc ∫⁻ y, ENNReal.ofReal (Real.pi * kerInner g t y ^ 2)
        ≤ ∫⁻ y, ENNReal.ofReal (Real.pi) *
            ENNReal.ofReal (∫ u, g u ^ 2 * heatKernel (t / 2) u y) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul Real.pi_pos.le]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (sq_kerInner_le_small hgi hg.bdd ht0 ht1 y) Real.pi_pos.le)
      _ ≤ ∫⁻ y, ENNReal.ofReal (Real.pi) *
            ∫⁻ u, ENNReal.ofReal (g u ^ 2) * ENNReal.ofReal (heatKernel (t / 2) u y) := by
          refine lintegral_mono fun y => ?_
          gcongr
          refine (ofReal_integral_le_lintegral fun u =>
            mul_nonneg (sq_nonneg _) (heatKernel_nonneg _ hs.le _ _)).trans (le_of_eq ?_)
          congr 1; funext u; rw [ENNReal.ofReal_mul (sq_nonneg _)]
      _ = ENNReal.ofReal (Real.pi) * ∫⁻ u, ENNReal.ofReal (g u ^ 2) := by
          have hgm := hg.meas
          rw [lintegral_const_mul _ (by
            refine Measurable.lintegral_prod_right' (f := fun q : ℂ × ℂ =>
              ENNReal.ofReal (g q.2 ^ 2) * ENNReal.ofReal (heatKernel (t / 2) q.2 q.1)) ?_
            unfold heatKernel; fun_prop)]
          congr 1
          rw [lintegral_lintegral_swap (by unfold heatKernel; fun_prop)]
          congr 1; funext u
          rw [lintegral_const_mul _ (by unfold heatKernel; fun_prop),
            lintegral_ofReal_heatKernel hs, mul_one]
      _ = ENNReal.ofReal (Real.pi * ∫ u, g u ^ 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hg2 (Eventually.of_forall fun u => sq_nonneg _),
            ENNReal.ofReal_mul Real.pi_pos.le]
  · -- large times
    have hsl : slicBound g t = (∫ u, |g u|) * (∫ u, |g u| * ‖u‖ ^ 2) / 2 * t ^ (-2 : ℝ) := by
      simp [slicBound, indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => by
        linarith [h.2]), indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht1)]
    rw [hsl]
    have hA : 0 ≤ ∫ u, |g u| := integral_nonneg fun _ => abs_nonneg _
    have hgn : Integrable fun u => |g u| * ‖u‖ ^ 2 := by
      have := hg.integrable_mul_bdd (f := fun u => ‖u‖ ^ 2) (by fun_prop) (K := R ^ 2)
        (fun u hu => by
          rw [abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) hu 2)
      refine this.abs.congr (Eventually.of_forall fun u => ?_)
      simp only [abs_mul, abs_pow, abs_norm]; ring
    have hmeasD : Measurable fun q : ℂ × ℂ =>
        (heatKernel (t / 2) q.1 q.2 - heatKernel (t / 2) 0 q.2) ^ 2 := by
      unfold heatKernel; fun_prop
    calc ∫⁻ y, ENNReal.ofReal (Real.pi * kerInner g t y ^ 2)
        ≤ ∫⁻ y, ENNReal.ofReal (Real.pi * ∫ u, |g u|) * ENNReal.ofReal
            (∫ u, |g u| * (heatKernel (t / 2) u y - heatKernel (t / 2) 0 y) ^ 2) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg Real.pi_pos.le hA)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (sq_kerInner_le_large hgi ht1 y) Real.pi_pos.le
      _ ≤ ∫⁻ y, ENNReal.ofReal (Real.pi * ∫ u, |g u|) * ∫⁻ u, ENNReal.ofReal (|g u|) *
            ENNReal.ofReal ((heatKernel (t / 2) u y - heatKernel (t / 2) 0 y) ^ 2) := by
          refine lintegral_mono fun y => ?_
          gcongr
          refine (ofReal_integral_le_lintegral fun u =>
            mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans (le_of_eq ?_)
          congr 1; funext u; rw [ENNReal.ofReal_mul (abs_nonneg _)]
      _ = ENNReal.ofReal (Real.pi * ∫ u, |g u|) * ∫⁻ u, ENNReal.ofReal (|g u|) *
            ∫⁻ y, ENNReal.ofReal ((heatKernel (t / 2) u y - heatKernel (t / 2) 0 y) ^ 2) := by
          have hgm := hg.meas
          rw [lintegral_const_mul _ (by
            refine Measurable.lintegral_prod_right' (f := fun q : ℂ × ℂ =>
              ENNReal.ofReal (|g q.2|) * ENNReal.ofReal
                ((heatKernel (t / 2) q.2 q.1 - heatKernel (t / 2) 0 q.1) ^ 2)) ?_
            unfold heatKernel; fun_prop)]
          congr 1
          rw [lintegral_lintegral_swap (by unfold heatKernel; fun_prop)]
          congr 1; funext u
          rw [lintegral_const_mul _ (by unfold heatKernel; fun_prop)]
      _ ≤ ENNReal.ofReal (Real.pi * ∫ u, |g u|) * ∫⁻ u, ENNReal.ofReal (|g u|) *
            ENNReal.ofReal (‖u‖ ^ 2 / (8 * Real.pi * (t / 2) ^ 2)) := by
          gcongr with u
          exact lintegral_ofReal_sq_heatKernel_sub_le hs u
      _ = ENNReal.ofReal (Real.pi * ∫ u, |g u|) *
            ENNReal.ofReal ((∫ u, |g u| * ‖u‖ ^ 2) / (8 * Real.pi * (t / 2) ^ 2)) := by
          congr 1
          rw [← integral_div, ofReal_integral_eq_lintegral_ofReal (hgn.div_const _)
            (Eventually.of_forall fun u => by positivity)]
          congr 1; funext u
          rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_div_assoc]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (mul_nonneg Real.pi_pos.le hA)]
          congr 1
          have ht' : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
            rw [Real.rpow_neg ht0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [ht']
          field_simp
          ring

lemma measurable_kerFun (hgm : Measurable g) : Measurable (kerFun g) := by
  have hK : Measurable fun q : ℝ × ℂ => kerInner g q.1 q.2 := by
    unfold kerInner
    refine (StronglyMeasurable.integral_prod_right' (f := fun p : (ℝ × ℂ) × ℂ => g p.2 *
      (heatKernel (p.1.1 / 2) p.2 p.1.2 - (Ioi (1 : ℝ)).indicator
        (fun _ => heatKernel (p.1.1 / 2) 0 p.1.2) p.1.1)) ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    refine (hgm.comp measurable_snd).mul ((by unfold heatKernel; fun_prop :
      Measurable fun p : (ℝ × ℂ) × ℂ => heatKernel (p.1.1 / 2) p.2 p.1.2).sub ?_)
    have e : (fun p : (ℝ × ℂ) × ℂ => (Ioi (1 : ℝ)).indicator
        (fun _ => heatKernel (p.1.1 / 2) 0 p.1.2) p.1.1) =
        {p : (ℝ × ℂ) × ℂ | 1 < p.1.1}.indicator (fun p => heatKernel (p.1.1 / 2) 0 p.1.2) := by
      funext p; simp [indicator]
    rw [e]
    exact (by unfold heatKernel; fun_prop : Measurable fun p : (ℝ × ℂ) × ℂ =>
      heatKernel (p.1.1 / 2) 0 p.1.2).indicator (measurableSet_lt measurable_const (by fun_prop))
  have e : kerFun g = fun q => Real.sqrt Real.pi *
      {q : ℝ × ℂ | 0 < q.1}.indicator (fun q => kerInner g q.1 q.2) q := by
    funext q; simp [kerFun, indicator]
  rw [e]
  exact measurable_const.mul (hK.indicator (measurableSet_lt measurable_const (by fun_prop)))

lemma integrable_slicBound (g : ℂ → ℝ) : Integrable (slicBound g) := by
  unfold slicBound
  refine Integrable.add ?_ ?_
  · exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  · exact (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _)

lemma integral_slicBound (g : ℂ → ℝ) : ∫ t, slicBound g t =
    Real.pi * (∫ u, g u ^ 2) + (∫ u, |g u|) * (∫ u, |g u| * ‖u‖ ^ 2) / 2 := by
  unfold slicBound
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp)))
    ((integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _)),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi, setIntegral_const,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  simp only [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one,
    smul_eq_mul, one_mul]
  norm_num

/-- **`L²` bound for the kernels.** `kerFun g ∈ L²(ℝ × ℂ)` and
`‖kerFun g‖² ≤ π ∫ g² + (∫ |g|)(∫ |g(u)| ‖u‖²)/2`. -/
theorem BddSupp.memLp_kerFun (hg : BddSupp g M R) :
    MemLp (kerFun g) 2 ∧ ∫ q, kerFun g q ^ 2 ≤
      Real.pi * (∫ u, g u ^ 2) + (∫ u, |g u|) * (∫ u, |g u| * ‖u‖ ^ 2) / 2 := by
  have hm := measurable_kerFun (g := g) hg.meas
  have hL : ∫⁻ q, ENNReal.ofReal (kerFun g q ^ 2) ≤ ENNReal.ofReal
      (Real.pi * (∫ u, g u ^ 2) + (∫ u, |g u|) * (∫ u, |g u| * ‖u‖ ^ 2) / 2) := by
    rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl]
    refine (lintegral_prod_le _).trans ?_
    refine (lintegral_mono fun t => lintegral_kerFun_slice_le hg t).trans (le_of_eq ?_)
    rw [← integral_slicBound, ofReal_integral_eq_lintegral_ofReal (integrable_slicBound g)
      (Eventually.of_forall fun t => ?_)]
    unfold slicBound
    refine add_nonneg (indicator_nonneg (fun _ _ => mul_nonneg Real.pi_pos.le
      (integral_nonneg fun _ => sq_nonneg _)) _) (indicator_nonneg (fun t ht => ?_) _)
    have : 0 < t := lt_trans one_pos ht
    have h1 : 0 ≤ ∫ u, |g u| := integral_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ ∫ u, |g u| * ‖u‖ ^ 2 := integral_nonneg fun _ => by positivity
    have h3 : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg this.le _
    positivity
  have hnn : 0 ≤ᵐ[volume] fun q => kerFun g q ^ 2 := Eventually.of_forall fun q => sq_nonneg _
  have hint : Integrable fun q => kerFun g q ^ 2 :=
    ⟨(hm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hm.pow_const 2).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hL
  have h1 : 0 ≤ ∫ u, |g u| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ u, |g u| * ‖u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h3 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := Real.pi_pos
  positivity

end GFFExist
end LQGMetric
