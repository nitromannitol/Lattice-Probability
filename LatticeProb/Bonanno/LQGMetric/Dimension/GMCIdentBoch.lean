/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentBoch at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentKer

/-!
# The kernel of a measure is the Bochner average of the point kernels (P2-GMCID, D67)

For a bounded open `A`, a time set `I ⊆ (c₀, ∞)` and a finite measure `μ` for which
`y ↦ K^I_y = 1_I(s) p_A(s/2; y, ·) ∈ L²` is Bochner integrable:

  `∫ K^I_y μ(dy) = K^I_μ` a.e. (`integral_wndKernelL2_ae_eq`), hence `K^I_μ ∈ L²` and
  `measKerL2 A I μ = ∫ K^I_y μ(dy)` (`measKerL2_eq_integral`).

Consequently `‖K^I_μ − K^I_z‖ ≤ ∫ ‖K^I_y − K^I_z‖ μ(dy)`, which with DZZ Lemma 2.5
(`pi_sq_norm_tildeHKernel_sub_le`) gives the convergence of the coarse part of the circle
average to `h̃_δ(z)` (the "continuity of `h^n`" in Berestycki arXiv:1506.09113 §4, l. 686).
Own elementary proof: integrals over finite-measure sets (`L2.inner_indicatorConstLp_one`), the
inner product commuting with the Bochner integral, Fubini, and
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

lemma measurable_wndKernel_uncurry {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable fun q : ℂ × (ℝ × ℂ) => wndKernel A I q.1 q.2 := by
  have e : (fun q : ℂ × (ℝ × ℂ) => wndKernel A I q.1 q.2) =
      ({q : ℂ × (ℝ × ℂ) | q.2.1 ∈ I}).indicator
        (fun q => killedHeat A (q.2.1 / 2).toNNReal q.1 q.2.2) := by
    funext q
    by_cases h : q.2.1 ∈ I <;> simp [wndKernel, h, Set.indicator]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage (measurable_fst.comp measurable_snd))
  exact (measurable_killedHeat hA).comp
    (((measurable_fst.comp measurable_snd).div_const 2).real_toNNReal.prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

lemma abs_wndKernel_le {A : Set ℂ} {I : Set ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hI0 : I ⊆ Ioi c₀)
    (y : ℂ) (p : ℝ × ℂ) : |wndKernel A I y p| ≤ (Real.pi * c₀)⁻¹ := by
  rw [abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
  by_cases hp : p.1 ∈ I
  · have h1 : c₀ < p.1 := hI0 hp
    refine (wndKernel_le A I y p (hc₀.trans h1)).trans ?_
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left h1.le Real.pi_pos.le)
  · simp [wndKernel, hp]; positivity

theorem integral_wndKernelL2_ae_eq {A : Set ℂ} (hA : IsOpen A) {cA : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball cA R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hFi : Integrable (fun y => wndKernelL2 A I y) μ) :
    ((∫ y, wndKernelL2 A I y ∂μ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] measKer A I μ := by
  set B : ℝ := (Real.pi * c₀)⁻¹
  have hjm := measurable_wndKernel_uncurry hA hI
  have hmm : Measurable (measKer A I μ) := by
    unfold measKer
    exact (hjm.stronglyMeasurable.integral_prod_left).measurable
  have hmb : ∀ p, ‖measKer A I μ p‖ ≤ μ.real univ * B := by
    intro p
    refine (norm_integral_le_of_norm_le_const (C := B) (Eventually.of_forall fun y => ?_)).trans
      (le_of_eq (by ring))
    rw [Real.norm_eq_abs]; exact abs_wndKernel_le hc₀ hI0 y p
  have hI0' : I ⊆ Ioi 0 := hI0.trans (Ioi_subset_Ioi hc₀.le)
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
    have hpt : ∀ y, ∫ p in E, (wndKernelL2 A I y : ℝ × ℂ → ℝ) p = ∫ p in E, wndKernel A I y p := by
      intro y
      have hmem := memLp_wndKernel hA hR hAR hI hc₀ hI0 y
      refine setIntegral_congr_ae hE ?_
      have : (wndKernelL2 A I y : ℝ × ℂ → ℝ) =ᵐ[volume] wndKernel A I y := by
        rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmem)]
        exact hmem.coeFn_toLp
      filter_upwards [this] with p hp _ using hp
    simp_rw [hpt]
    have : Fact (volume E < ∞) := ⟨hEf⟩
    have hint : Integrable (Function.uncurry fun y p => wndKernel A I y p)
        (μ.prod (volume.restrict E)) := by
      refine Integrable.of_bound (C := B) hjm.aestronglyMeasurable
        (Eventually.of_forall fun q => ?_)
      rw [Real.norm_eq_abs]; exact abs_wndKernel_le hc₀ hI0 q.1 q.2
    rw [integral_integral_swap hint]
    rfl

theorem measKerL2_eq_integral {A : Set ℂ} (hA : IsOpen A) {cA : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hAR : A ⊆ Metric.ball cA R) {I : Set ℝ} (hI : MeasurableSet I) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hI0 : I ⊆ Ioi c₀) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hFi : Integrable (fun y => wndKernelL2 A I y) μ) :
    MemLp (measKer A I μ) 2 volume ∧ measKerL2 A I μ = ∫ y, wndKernelL2 A I y ∂μ := by
  have h := integral_wndKernelL2_ae_eq hA hR hAR hI hc₀ hI0 μ hFi
  have hm : MemLp (measKer A I μ) 2 volume := (Lp.memLp _).ae_eq h
  refine ⟨hm, ?_⟩
  rw [measKerL2, dite_eq_left_of_eq_true (eq_true hm)]
  rw [← Lp.toLp_coeFn (∫ y, wndKernelL2 A I y ∂μ) (Lp.memLp _)]
  exact MemLp.toLp_congr _ _ h.symm

section Circle

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma norm_tildeKer_sub_le (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    ‖wndKernelL2 openSquare (Ioi (δ ^ 2)) u - wndKernelL2 openSquare (Ioi (δ ^ 2)) v‖ ≤
      Real.sqrt (28 * ‖u - v‖ / (Real.pi * δ)) := by
  have h := pi_sq_norm_tildeHKernel_sub_le hW hδ u v
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ (by positivity)]
  have := mul_comm Real.pi (‖wndKernelL2 openSquare (Ioi (δ ^ 2)) u -
    wndKernelL2 openSquare (Ioi (δ ^ 2)) v‖ ^ 2)
  rw [le_div_iff₀ hδ] at h
  nlinarith [h]

lemma continuous_tildeKer (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun y => wndKernelL2 openSquare (Ioi (δ ^ 2)) y := by
  rw [Metric.continuous_iff]
  intro v ε hε
  refine ⟨ε ^ 2 * (Real.pi * δ) / 28, by positivity, fun u hu => ?_⟩
  rw [dist_eq_norm] at hu ⊢
  refine (norm_tildeKer_sub_le hW hδ u v).trans_lt ?_
  rw [show ε = Real.sqrt (ε ^ 2) from (Real.sqrt_sq hε.le).symm]
  refine Real.sqrt_lt_sqrt (by positivity) ?_
  rw [div_lt_iff₀ (by positivity)]
  rw [lt_div_iff₀ (by norm_num)] at hu
  linarith

/-- **Coarse part of a small circle average**: for a probability measure `μ` carried by
`B̄(z, r)`, `‖K^{(δ²,∞)}_μ − K^{(δ²,∞)}_z‖ ≤ √(28 r/(π δ))` (DZZ Lemma 2.5 averaged over `μ`). -/
theorem norm_measKerL2_sub_tildeKer_le (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    {r : ℝ} (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hμ : μ (Metric.closedBall z r)ᶜ = 0) :
    MemLp (measKer openSquare (Ioi (δ ^ 2)) μ) 2 volume ∧
    ‖measKerL2 openSquare (Ioi (δ ^ 2)) μ - wndKernelL2 openSquare (Ioi (δ ^ 2)) z‖ ≤
      Real.sqrt (28 * r / (Real.pi * δ)) := by
  set K := fun y => wndKernelL2 openSquare (Ioi (δ ^ 2)) y
  have hK := continuous_tildeKer hW hδ
  have hae : ∀ᵐ y ∂μ, y ∈ Metric.closedBall z r := by
    rw [ae_iff]; simpa [compl_def] using hμ
  have hbd : ∀ᵐ y ∂μ, ‖K y - K z‖ ≤ Real.sqrt (28 * r / (Real.pi * δ)) := by
    filter_upwards [hae] with y hy
    refine (norm_tildeKer_sub_le hW hδ y z).trans (Real.sqrt_le_sqrt ?_)
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    gcongr
  have hFi : Integrable K μ := by
    refine Integrable.of_bound hK.aestronglyMeasurable
      (C := ‖K z‖ + Real.sqrt (28 * r / (Real.pi * δ))) ?_
    filter_upwards [hbd] with y hy
    calc ‖K y‖ = ‖(K y - K z) + K z‖ := by rw [sub_add_cancel]
      _ ≤ ‖K y - K z‖ + ‖K z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  obtain ⟨hm, he⟩ := measKerL2_eq_integral isOpen_openSquare (R := 2) (by norm_num)
    openSquare_subset_ball measurableSet_Ioi hδ2 subset_rfl μ hFi
  refine ⟨hm, ?_⟩
  rw [he]
  have e : (∫ y, K y ∂μ) - K z = ∫ y, (K y - K z) ∂μ := by
    rw [integral_sub hFi (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e]
  refine (norm_integral_le_of_norm_le_const hbd).trans (le_of_eq ?_)
  rw [probReal_univ, mul_one]

end Circle

end GMCIdent
end LQGMetric
