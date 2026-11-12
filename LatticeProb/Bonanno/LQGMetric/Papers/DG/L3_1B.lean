/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAShell

/-!
# The kernel of `h^U − ĥ^tr` integrated against a measure (task P2-DG3E)

DG (`metric-comparison-final.tex`, (3.4) DG:950 with `t = 0`, and the proof of Lemma A.1
DG:2146): `ĥ^tr = √π ∫_0^1 ∫ p_{B_{1/10}(·)}(s/2; ·, w) W(dw, ds)`. Its point kernel is
`trKer z = wndKernel (B(z,1/10)) (0,1] z`; the kernel `dgA1Kernel U z` of `h^U − ĥ^tr` (AppA1Main)
is a.e. `wndKernel U (Ioi 0) z − trKer z` (`dgA1Kernel_ae_eq`), and for a finite measure `μ`
carried by `{z : B(z,1/10) ⊆ U}` its Bochner integral is a.e. `measKer U (Ioi 0) μ − trMeasKer μ`,
the kernel of `(h^U, μ) − (ĥ^tr, μ)` (`integral_dgA1Kernel_ae_eq`). Same proof as
`integral_dgUHatKernel_ae_eq` (AppA3Ker); own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent

/-- translation of the centred killed kernel of a ball -/
lemma killedHeat_ball_translate (t : ℝ≥0) (c w : ℂ) (ρ : ℝ) :
    killedHeat (Metric.ball c ρ) t c w = killedHeat (Metric.ball 0 ρ) t 0 (w - c) := by
  unfold killedHeat
  rw [bridgeStay_ball_translate]
  congr 1
  unfold heatKernel
  rw [zero_sub, norm_neg, norm_sub_rev]

/-- the kernel of `ĥ^tr(z) = √π ∫_0^1 ∫ p_{B_{1/10}(z)}(s/2; z, w) W(dw, ds)` (DG (3.4), `t = 0`) -/
def trKer (z : ℂ) (p : ℝ × ℂ) : ℝ := wndKernel (Metric.ball z (1 / 10)) (Ioc 0 1) z p

/-- the kernel of `(ĥ^tr, μ)` -/
def trMeasKer (μ : Measure ℂ) (p : ℝ × ℂ) : ℝ := ∫ z, trKer z p ∂μ

open Classical in
/-- the `L²` class of `trMeasKer μ` (junk `0` if it is not square integrable) -/
def trMeasKerL2 (μ : Measure ℂ) : WNSpace :=
  if h : MemLp (trMeasKer μ) 2 volume then h.toLp _ else 0

lemma measurable_trKer_uncurry : Measurable fun q : ℂ × (ℝ × ℂ) => trKer q.1 q.2 := by
  have e : (fun q : ℂ × (ℝ × ℂ) => trKer q.1 q.2) =
      ({q : ℂ × (ℝ × ℂ) | q.2.1 ∈ Ioc (0 : ℝ) 1}).indicator
        (fun q => killedHeat (Metric.ball 0 (1 / 10)) (q.2.1 / 2).toNNReal 0 (q.2.2 - q.1)) := by
    funext q
    by_cases h : q.2.1 ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem (show q ∈ {q : ℂ × (ℝ × ℂ) | q.2.1 ∈ Ioc (0 : ℝ) 1} from h)]
      simp only [trKer, wndKernel]; rw [indicator_of_mem h, killedHeat_ball_translate]
    · rw [indicator_of_notMem (show q ∉ {q : ℂ × (ℝ × ℂ) | q.2.1 ∈ Ioc (0 : ℝ) 1} from h)]
      simp only [trKer, wndKernel]; rw [indicator_of_notMem h]
  rw [e]
  refine Measurable.indicator ?_
    (measurableSet_Ioc.preimage (measurable_fst.comp measurable_snd))
  exact (measurable_killedHeat Metric.isOpen_ball).comp
    (((measurable_fst.comp measurable_snd).div_const 2).real_toNNReal.prodMk
      (measurable_const.prodMk ((measurable_snd.comp measurable_snd).sub measurable_fst)))

lemma trKer_nonneg (z : ℂ) (p : ℝ × ℂ) : 0 ≤ trKer z p := wndKernel_nonneg _ _ _ _

lemma trKer_le_hatKer (z : ℂ) (p : ℝ × ℂ) : trKer z p ≤ hatKer z p := by
  obtain ⟨s, w⟩ := p
  by_cases h : s ∈ Ioc (0 : ℝ) 1
  · simp only [trKer, wndKernel, hatKer]
    rw [indicator_of_mem h, indicator_of_mem h]
    have := killedHeat_le_heatKernel (Metric.ball z (1 / 10)) (s / 2).toNNReal z w
    rwa [Real.coe_toNNReal _ (by linarith [h.1])] at this
  · simp only [trKer, wndKernel, hatKer]
    rw [indicator_of_notMem h, indicator_of_notMem h]

lemma wndKernel_le_inv_add_hatKer (U : Set ℂ) (z : ℂ) (p : ℝ × ℂ) :
    wndKernel U (Ioi 0) z p ≤ Real.pi⁻¹ + hatKer z p := by
  have hpi := Real.pi_pos
  obtain ⟨s, w⟩ := p
  by_cases h0 : 0 < s
  · by_cases h1 : s ≤ 1
    · have hm : s ∈ Ioc (0 : ℝ) 1 := ⟨h0, h1⟩
      have ew : wndKernel U (Ioi 0) z (s, w) = killedHeat U (s / 2).toNNReal z w := by
        simp [wndKernel, h0]
      have eh : hatKer z (s, w) = heatKernel (s / 2) z w := by
        simp only [hatKer]; rw [indicator_of_mem hm]
      have hle : killedHeat U (s / 2).toNNReal z w ≤ heatKernel (s / 2) z w := by
        have := killedHeat_le_heatKernel U (s / 2).toNNReal z w
        rwa [Real.coe_toNNReal _ (by linarith)] at this
      rw [ew, eh]; linarith [inv_pos.2 hpi]
    · refine (wndKernel_le U _ z (s, w) h0).trans ?_
      have : (Real.pi * s)⁻¹ ≤ Real.pi⁻¹ :=
        inv_anti₀ hpi (le_mul_of_one_le_right hpi.le (by simpa using (not_le.1 h1).le))
      linarith [hatKer_nonneg z (s, w)]
  · have ew : wndKernel U (Ioi 0) z (s, w) = 0 := by simp [wndKernel, h0]
    rw [ew]; linarith [inv_pos.2 hpi, hatKer_nonneg z (s, w)]

lemma abs_wnd_sub_trKer_le (U : Set ℂ) (z : ℂ) (p : ℝ × ℂ) :
    |wndKernel U (Ioi 0) z p - trKer z p| ≤ Real.pi⁻¹ + 2 * hatKer z p := by
  have h1 := wndKernel_le_inv_add_hatKer U z p
  have h2 := trKer_le_hatKer z p
  have h3 := wndKernel_nonneg U (Ioi 0) z p
  have h4 := trKer_nonneg z p
  rw [abs_le]; constructor <;> linarith

/-- pointwise form of the kernel of `h^U − ĥ^tr` -/
theorem dgA1Kernel_ae_eq {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {z : ℂ} (hz : Metric.ball z (1 / 10) ⊆ U) :
    (dgA1Kernel U z : ℝ × ℂ → ℝ) =ᵐ[volume] fun p => wndKernel U (Ioi 0) z p - trKer z p := by
  have hmem := memLp_wndKernel hU hR hUR (measurableSet_Ioi (a := (1 : ℝ))) (c₀ := 1 / 2)
    (by norm_num) (Ioi_subset_Ioi (by norm_num)) z
  have h3 : (wndKernelL2 U (Ioi 1) z : ℝ × ℂ → ℝ) =ᵐ[volume] wndKernel U (Ioi 1) z := by
    rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmem)]; exact hmem.coeFn_toLp
  have h4 : (kernelU0 U z : ℝ × ℂ → ℝ) =ᵐ[volume] kerIU U (Ioc 0 1) z := by
    rw [kernelU0_eq hU hz]; exact MemLp.coeFn_toLp _
  unfold dgA1Kernel
  filter_upwards [Lp.coeFn_add (wndKernelL2 U (Ioi 1) z) (kernelU0 U z), h3, h4] with p h2 e3 e4
  rw [h2, Pi.add_apply, e3, e4]
  obtain ⟨s, w⟩ := p
  simp only [wndKernel, kerIU, trKer, kerU, indicator, mem_Ioi, mem_Ioc]
  by_cases h0 : 0 < s
  · by_cases h1' : s ≤ 1
    · simp [h0, h1', not_lt.2 h1']
    · simp [h0, h1', lt_of_not_ge h1']
  · simp [h0, show ¬ 1 < s by linarith]

/-- the Bochner integral of the kernel of `h^U − ĥ^tr` against `μ` is the kernel of
`(h^U, μ) − (ĥ^tr, μ)` -/
theorem integral_dgA1Kernel_ae_eq {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, Metric.ball z (1 / 10) ⊆ U) (hk : Integrable (dgA1Kernel U) μ) :
    ((∫ z, dgA1Kernel U z ∂μ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun p => measKer U (Ioi 0) μ p - trMeasKer μ p := by
  have hpi := Real.pi_pos
  set F : ℂ × (ℝ × ℂ) → ℝ := fun q => wndKernel U (Ioi 0) q.1 q.2 - trKer q.1 q.2 with hF
  have hm1 := measurable_wndKernel_uncurry hU (measurableSet_Ioi (a := (0 : ℝ)))
  have hm2 := measurable_trKer_uncurry
  have hFm : Measurable F := hm1.sub hm2
  have hpt : ∀ p, ∫ z, F (z, p) ∂μ = measKer U (Ioi 0) μ p - trMeasKer μ p := by
    intro p
    have i1 : Integrable (fun z => wndKernel U (Ioi 0) z p) μ := by
      by_cases hp : 0 < p.1
      · refine Integrable.of_bound (Measurable.of_uncurry_right hm1).aestronglyMeasurable
          (Real.pi * p.1)⁻¹ (Eventually.of_forall fun z => ?_)
        rw [Real.norm_of_nonneg (wndKernel_nonneg _ _ _ _)]; exact wndKernel_le U _ z p hp
      · have : (fun z => wndKernel U (Ioi 0) z p) = fun _ => 0 := by
          funext z; simp [wndKernel, hp]
        rw [this]; exact integrable_zero _ _ _
    have i2 : Integrable (fun z => trKer z p) μ := by
      by_cases hp : 0 < p.1
      · refine Integrable.of_bound (Measurable.of_uncurry_right hm2).aestronglyMeasurable
          (Real.pi * p.1)⁻¹ (Eventually.of_forall fun z => ?_)
        rw [Real.norm_of_nonneg (trKer_nonneg _ _)]; exact wndKernel_le _ _ z p hp
      · have : (fun z => trKer z p) = fun _ => 0 := by
          funext z; simp only [trKer, wndKernel]; rw [indicator_of_notMem (fun h => hp h.1)]
        rw [this]; exact integrable_zero _ _ _
    exact integral_sub i1 i2
  have hint : ∀ E : Set (ℝ × ℂ), MeasurableSet E → volume E < ∞ →
      Integrable F (μ.prod (volume.restrict E)) := by
    intro E hE hEf
    have : Fact (volume E < ∞) := ⟨hEf⟩
    have e : μ.prod (volume.restrict E) = (μ.prod volume).restrict (univ ×ˢ E) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hG : Integrable (fun q : ℂ × (ℝ × ℂ) => Real.pi⁻¹ + 2 * hatKer q.1 q.2)
        (μ.prod (volume.restrict E)) := by
      refine (integrable_const _).add (Integrable.const_mul ?_ 2)
      rw [e]; exact (integrable_hatKer_prod μ).restrict
    refine hG.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]; exact abs_wnd_sub_trKer_le U q.1 q.2
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun E hE hEf => ?_)
    (fun E hE hEf => ?_) (fun E hE hEf => ?_)
  · have : Fact (volume E < ∞) := ⟨hEf⟩
    exact ((Lp.memLp _).restrict E).integrable one_le_two
  · exact ((hint E hE hEf).integral_prod_right).congr (Eventually.of_forall hpt)
  · rw [← L2.inner_indicatorConstLp_one hE hEf.ne,
      ← integral_inner (𝕜 := ℝ) hk (indicatorConstLp 2 hE hEf.ne (1 : ℝ))]
    simp_rw [L2.inner_indicatorConstLp_one hE hEf.ne]
    have h1 : ∀ᵐ z ∂μ, ∫ p in E, (dgA1Kernel U z : ℝ × ℂ → ℝ) p = ∫ p in E, F (z, p) := by
      filter_upwards [hμ] with z hz
      refine setIntegral_congr_ae hE ?_
      filter_upwards [dgA1Kernel_ae_eq hU hR hUR hz] with p hp _ using hp
    rw [integral_congr_ae h1]
    rw [integral_integral_swap (f := fun z p => F (z, p)) (hint E hE hEf)]
    exact setIntegral_congr_fun hE fun p _ => hpt p

end DG
end LQGMetric
