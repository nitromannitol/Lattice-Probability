/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1C1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B3
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernelL2

/-!
# DG Lemma 3.1, the pair `(h, ĥ)`: the large-time kernel (task P2-DG105e, D109)

With the whole-plane GFF built from the white noise `W` of `ĥ` (`Field/ExistGFF`,
`h₀(φ) = W(kerFun φ)`, `kerFun g (t,y) = √π 1_{t>0} ∫ g(u)(p_{t/2}(u,y) − 1_{t>1} p_{t/2}(0,y)) du`),
`h₀ − ĥ` is the large-time field with point kernel

  `largeKer u (t, y) = 1_{t>1} (p_{t/2}(u, y) − p_{t/2}(0, y))`.

* `abs_largeKer_le`: `|largeKer u q| ≤ π⁻¹`;
* `lintegral_sq_largeKer_sub_le`: `∫∫ (largeKer x − largeKer c)² ≤ |x − c|² / (2π)`
  (`∫ (p_s(x,·) − p_s(c,·))² ≤ |x−c|²/(8πs²)`, `ExistKernel.integral_sq_heatKernel_sub_le`, and
  `∫_1^∞ t^{-2} dt = 1`);
* `largeKerL2`, `norm_largeKerL2_sub_sq_le`, `lipschitzWith_largeKerL2`;
* `integral_L2_ae_eq_of_bdd`: the Bochner integral of `L²`-classes of a bounded jointly
  measurable kernel is a.e. the pointwise integral (pattern of `GMCIdent.integral_wndKernelL2_ae_eq`).

DG (`metric-comparison-final.tex`) Lemma 3.1, DG:966–976; own elementary arguments (DEVIATIONS:
the coupling of `h` with the white noise, D109).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DG

open WhiteNoise GFFExist DZZ QuantumZipper SupTail

/-- the large-time kernel `1_{t>1} (p_{t/2}(u,y) − p_{t/2}(0,y))` of `h₀ − ĥ` -/
def largeKer (u : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Ioi (1 : ℝ)).indicator (fun t => heatKernel (t / 2) u q.2 - heatKernel (t / 2) 0 q.2) q.1

lemma measurable_largeKer_uncurry : Measurable fun q : ℂ × (ℝ × ℂ) => largeKer q.1 q.2 := by
  have e : (fun q : ℂ × (ℝ × ℂ) => largeKer q.1 q.2) =
      ({q : ℂ × (ℝ × ℂ) | q.2.1 ∈ Ioi (1 : ℝ)}).indicator
        (fun q => heatKernel (q.2.1 / 2) q.1 q.2.2 - heatKernel (q.2.1 / 2) 0 q.2.2) := by
    funext q; simp [largeKer, indicator]
  rw [e]
  refine Measurable.indicator ?_ (measurableSet_Ioi.preimage (measurable_fst.comp measurable_snd))
  unfold heatKernel; fun_prop

lemma measurable_largeKer (u : ℂ) : Measurable (largeKer u) := by
  have e : largeKer u = ({q : ℝ × ℂ | q.1 ∈ Ioi (1 : ℝ)}).indicator
      (fun q => heatKernel (q.1 / 2) u q.2 - heatKernel (q.1 / 2) 0 q.2) := by
    funext q; simp [largeKer, indicator]
  rw [e]
  refine Measurable.indicator ?_ (measurableSet_Ioi.preimage measurable_fst)
  unfold heatKernel; fun_prop

lemma abs_largeKer_le (u : ℂ) (q : ℝ × ℂ) : |largeKer u q| ≤ Real.pi⁻¹ := by
  unfold largeKer
  by_cases h : q.1 ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem h]
    have ht : (1 : ℝ) < q.1 := h
    have hs : 0 < q.1 / 2 := by linarith
    have hle : (2 * Real.pi * (q.1 / 2))⁻¹ ≤ Real.pi⁻¹ :=
      inv_anti₀ Real.pi_pos (by nlinarith [Real.pi_pos])
    exact abs_sub_le_of_nonneg_of_le (heatKernel_nonneg _ hs.le _ _)
      ((heatKernel_le _ hs _ _).trans hle) (heatKernel_nonneg _ hs.le _ _)
      ((heatKernel_le _ hs _ _).trans hle)
  · rw [indicator_of_notMem h, abs_zero]; positivity

lemma heatKernel_translate (s : ℝ) (x c y : ℂ) :
    heatKernel s x (y + c) = heatKernel s (x - c) y := by
  simp only [heatKernel]
  congr 3
  congr 2
  ring_nf

/-- one time slice -/
lemma lintegral_sq_largeKer_sub_slice (x c : ℂ) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal ((largeKer x (t, y) - largeKer c (t, y)) ^ 2) ≤
      (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (‖x - c‖ ^ 2 / (2 * Real.pi) *
        t ^ (-2 : ℝ))) t := by
  by_cases h : t ∈ Ioi (1 : ℝ)
  · have ht : (1 : ℝ) < t := h
    have hs : 0 < t / 2 := by linarith
    rw [indicator_of_mem h]
    simp only [largeKer, indicator_of_mem h]
    have e : ∀ y, (heatKernel (t / 2) x y - heatKernel (t / 2) 0 y -
        (heatKernel (t / 2) c y - heatKernel (t / 2) 0 y)) ^ 2 =
        (fun y => (heatKernel (t / 2) (x - c) y - heatKernel (t / 2) 0 y) ^ 2) (y - c) := by
      intro y
      have h1 := heatKernel_translate (t / 2) x c (y - c)
      have h2 := heatKernel_translate (t / 2) c c (y - c)
      rw [sub_add_cancel] at h1 h2
      simp only [sub_self] at h2
      rw [h1, h2]; ring
    simp_rw [e]
    rw [lintegral_sub_right_eq_self (fun y => ENNReal.ofReal
      ((heatKernel (t / 2) (x - c) y - heatKernel (t / 2) 0 y) ^ 2)) c]
    refine (lintegral_ofReal_sq_heatKernel_sub_le hs (x - c)).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.rpow_neg (by linarith), Real.rpow_two]
    field_simp
    ring
  · rw [indicator_of_notMem h]
    simp [largeKer, indicator_of_notMem h]

lemma lintegral_sq_largeKer_sub_le (x c : ℂ) :
    ∫⁻ q, ENNReal.ofReal ((largeKer x q - largeKer c q) ^ 2) ≤
      ENNReal.ofReal (‖x - c‖ ^ 2 / (2 * Real.pi)) := by
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_mono fun t => lintegral_sq_largeKer_sub_slice x c t).trans (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Ioi]
  have hi : IntegrableOn (fun t : ℝ => ‖x - c‖ ^ 2 / (2 * Real.pi) * t ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have : 0 < t := lt_trans one_pos ht
    have := Real.rpow_nonneg this.le (-2 : ℝ)
    simp only [Pi.zero_apply]; positivity

lemma memLp_sub_largeKer (x c : ℂ) :
    MemLp (fun q => largeKer x q - largeKer c q) 2 (volume : Measure (ℝ × ℂ)) := by
  have hm : Measurable fun q => largeKer x q - largeKer c q :=
    (measurable_largeKer x).sub (measurable_largeKer c)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨(hm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun q => sq_nonneg _)).2
    ((lintegral_sq_largeKer_sub_le x c).trans_lt ENNReal.ofReal_lt_top)⟩

lemma largeKer_zero (q : ℝ × ℂ) : largeKer 0 q = 0 := by simp [largeKer]

lemma memLp_largeKer (u : ℂ) : MemLp (largeKer u) 2 (volume : Measure (ℝ × ℂ)) := by
  have := memLp_sub_largeKer u 0
  simpa only [largeKer_zero, sub_zero] using this

/-- the `L²` class of `largeKer u` -/
def largeKerL2 (u : ℂ) : WNSpace := (memLp_largeKer u).toLp _

lemma coeFn_largeKerL2 (u : ℂ) :
    (largeKerL2 u : ℝ × ℂ → ℝ) =ᵐ[volume] largeKer u := (memLp_largeKer u).coeFn_toLp

lemma norm_sq_eq_integral (f : WNSpace) : ‖f‖ ^ 2 = ∫ q, (f q) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp [sq]

lemma norm_largeKerL2_sub_sq_le (x c : ℂ) :
    ‖largeKerL2 x - largeKerL2 c‖ ^ 2 ≤ ‖x - c‖ ^ 2 / (2 * Real.pi) := by
  rw [norm_sq_eq_integral]
  have e : (fun q => ((largeKerL2 x - largeKerL2 c : WNSpace) q) ^ 2) =ᵐ[volume]
      fun q => (largeKer x q - largeKer c q) ^ 2 := by
    filter_upwards [Lp.coeFn_sub (largeKerL2 x) (largeKerL2 c), coeFn_largeKerL2 x,
      coeFn_largeKerL2 c] with q h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [integral_congr_ae e, integral_eq_lintegral_of_nonneg_ae
    (f := fun q => (largeKer x q - largeKer c q) ^ 2) (Eventually.of_forall fun q => sq_nonneg _)
    ((((measurable_largeKer x).sub (measurable_largeKer c)).pow_const 2).aestronglyMeasurable)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_sq_largeKer_sub_le x c)).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma lipschitzWith_largeKerL2 :
    LipschitzWith ⟨(Real.sqrt (2 * Real.pi))⁻¹, by positivity⟩ largeKerL2 := by
  refine LipschitzWith.of_dist_le_mul fun x c => ?_
  rw [dist_eq_norm, dist_eq_norm]
  change ‖largeKerL2 x - largeKerL2 c‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * ‖x - c‖
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (two_ne_zero)).1 ?_
  refine (norm_largeKerL2_sub_sq_le x c).trans (le_of_eq ?_)
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  ring

lemma continuous_largeKerL2 : Continuous largeKerL2 := lipschitzWith_largeKerL2.continuous

/-- the Hölder input of `exists_box_modification_tail` on a box -/
lemma norm_largeKerL2_sub_sq_le_box {y : ℂ} {b : ℝ} {x c : ℂ} (hx : x ∈ ferniqueBox y b)
    (hc : c ∈ ferniqueBox y b) :
    ‖largeKerL2 x - largeKerL2 c‖ ^ 2 ≤ 2 * b / (2 * Real.pi) * ‖x - c‖ := by
  refine (norm_largeKerL2_sub_sq_le x c).trans ?_
  have hd := norm_sub_le_of_mem_box hx hc
  have h0 := norm_nonneg (x - c)
  rw [div_mul_eq_mul_div, sq]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- an `E`-valued continuous function is integrable for the circle measure -/
lemma integrable_circleUnif_of_continuous' {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Continuous f) {z : ℂ} {r : ℝ} (hr : 0 < r) : Integrable f (circleUnif z r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hf.continuousOn
  have hae : ∀ᵐ x ∂(circleUnif z r), x ∈ Metric.closedBall z r :=
    mem_ae_iff.2 (circleUnif_compl_closedBall hr z)
  exact Integrable.of_bound hf.aestronglyMeasurable M (hae.mono fun x hx => hM x hx)

/-- **Bochner integral of `L²` kernels**: for a bounded jointly measurable kernel `f` and `L²`
classes `F u = f u` a.e., `∫ F dμ = ∫ f(u, ·) μ(du)` a.e. -/
theorem integral_L2_ae_eq_of_bdd {μ : Measure ℂ} [IsFiniteMeasure μ] {f : ℂ → ℝ × ℂ → ℝ}
    (hjm : Measurable fun q : ℂ × (ℝ × ℂ) => f q.1 q.2) {B : ℝ} (hB : ∀ u q, |f u q| ≤ B)
    {F : ℂ → WNSpace} (hF : ∀ u, (F u : ℝ × ℂ → ℝ) =ᵐ[volume] f u) (hFi : Integrable F μ) :
    ((∫ u, F u ∂μ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] fun q => ∫ u, f u q ∂μ := by
  have hmm : Measurable fun q => ∫ u, f u q ∂μ :=
    (hjm.stronglyMeasurable.integral_prod_left).measurable
  have hmb : ∀ q, ‖∫ u, f u q ∂μ‖ ≤ μ.real univ * B := by
    intro q
    refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun u => ?_)).trans
      (le_of_eq (by ring))
    rw [Real.norm_eq_abs]; exact hB u q
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun E hE hEf => ?_)
    (fun E hE hEf => ?_) (fun E hE hEf => ?_)
  · have : Fact (volume E < ∞) := ⟨hEf⟩
    exact ((Lp.memLp _).restrict E).integrable one_le_two
  · have : Fact (volume E < ∞) := ⟨hEf⟩
    exact Integrable.of_bound hmm.aestronglyMeasurable (C := μ.real univ * B)
      (Eventually.of_forall hmb)
  · rw [← L2.inner_indicatorConstLp_one hE hEf.ne]
    have hc := (innerSL ℝ (indicatorConstLp 2 hE hEf.ne (1 : ℝ))).integral_comp_comm hFi
    simp only [innerSL_apply_apply] at hc
    rw [← hc]
    simp_rw [L2.inner_indicatorConstLp_one hE hEf.ne]
    have hpt : ∀ u, ∫ q in E, (F u : ℝ × ℂ → ℝ) q = ∫ q in E, f u q := by
      intro u
      refine setIntegral_congr_ae hE ?_
      filter_upwards [hF u] with q hq _ using hq
    simp_rw [hpt]
    have : Fact (volume E < ∞) := ⟨hEf⟩
    have hint : Integrable (Function.uncurry fun u q => f u q) (μ.prod (volume.restrict E)) := by
      refine Integrable.of_bound (C := B) hjm.aestronglyMeasurable
        (Eventually.of_forall fun q => ?_)
      rw [Real.norm_eq_abs]; exact hB q.1 q.2
    rw [integral_integral_swap hint]

lemma integral_largeKerL2_ae_eq (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hFi : Integrable largeKerL2 μ) :
    ((∫ u, largeKerL2 u ∂μ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] fun q => ∫ u, largeKer u q ∂μ :=
  integral_L2_ae_eq_of_bdd measurable_largeKer_uncurry abs_largeKer_le coeFn_largeKerL2 hFi

end DG
end LQGMetric
