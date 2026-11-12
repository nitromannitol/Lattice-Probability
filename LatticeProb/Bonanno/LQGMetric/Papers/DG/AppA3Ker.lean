/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA3Ker at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAPair
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentBoch
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernel

/-!
DG (`metric-comparison-final.tex`, (3.1) DG:917 and the proof of Lemma A.1 DG:2146):
`ĥ = √π ∫_0^1 ∫ p_{s/2}(·, w) W(dw, ds)` and `h^U = √π ∫_0^∞ ∫ p_U(s/2; ·, w) W(dw, ds)`.
The point kernel `dgUHatKernel U z` of `h^U − ĥ` (AppAPair) is a.e. the function
`wndKernel U (Ioi 0) z − hatKer z` (`dgUHatKernel_ae_eq`), and for a finite measure `μ` carried
by `{z : B(z,1/10) ⊆ U}` its Bochner integral is a.e. `measKer U (Ioi 0) μ − hatMeasKer μ`, the
kernel of `(h^U, μ) − (ĥ, μ)` (`integral_dgUHatKernel_ae_eq`). Same proof pattern as
`GMCIdentBoch.integral_wndKernelL2_ae_eq` (test sets of finite measure, Fubini); own elementary
argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent

/-- the kernel of `ĥ(z) = √π ∫_0^1 ∫ p_{s/2}(z, w) W(dw, ds)` (DG (3.1)) -/
def hatKer (z : ℂ) (p : ℝ × ℂ) : ℝ := (Ioc (0 : ℝ) 1).indicator (fun s => heatKernel (s / 2) z p.2) p.1

/-- the kernel of `(ĥ, μ)` -/
def hatMeasKer (μ : Measure ℂ) (p : ℝ × ℂ) : ℝ := ∫ z, hatKer z p ∂μ

open Classical in
/-- the `L²` class of `hatMeasKer μ` (junk `0` if it is not square integrable) -/
def hatMeasKerL2 (μ : Measure ℂ) : WNSpace :=
  if h : MemLp (hatMeasKer μ) 2 volume then h.toLp _ else 0

lemma hatKer_nonneg (z : ℂ) (p : ℝ × ℂ) : 0 ≤ hatKer z p := by
  unfold hatKer
  by_cases h : p.1 ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem h]; exact heatKernel_nonneg _ (by linarith [h.1]) _ _
  · rw [indicator_of_notMem h]

lemma hatKer_le (z : ℂ) (p : ℝ × ℂ) (hp : 0 < p.1) : hatKer z p ≤ (Real.pi * p.1)⁻¹ := by
  unfold hatKer
  by_cases h : p.1 ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem h]
    refine (GFFExist.heatKernel_le _ (by linarith) _ _).trans (le_of_eq ?_)
    congr 1; ring
  · rw [indicator_of_notMem h]; positivity

lemma measurable_hatKer_uncurry : Measurable fun q : ℂ × (ℝ × ℂ) => hatKer q.1 q.2 := by
  have e : (fun q : ℂ × (ℝ × ℂ) => hatKer q.1 q.2) =
      ({q : ℂ × (ℝ × ℂ) | q.2.1 ∈ Ioc (0 : ℝ) 1}).indicator
        (fun q => heatKernel (q.2.1 / 2) q.1 q.2.2) := by
    funext q; simp [hatKer, indicator]
  rw [e]
  refine Measurable.indicator ?_ (measurableSet_Ioc.preimage (measurable_fst.comp measurable_snd))
  unfold heatKernel; fun_prop

/-- pointwise form of the kernel of `h^U − ĥ` -/
theorem dgUHatKernel_ae_eq {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {z : ℂ} (hz : Metric.ball z (1 / 10) ⊆ U) :
    (dgUHatKernel U z : ℝ × ℂ → ℝ) =ᵐ[volume] fun p => wndKernel U (Ioi 0) z p - hatKer z p := by
  have hmem := memLp_wndKernel hU hR hUR (measurableSet_Ioi (a := (1 : ℝ))) (c₀ := 1 / 2)
    (by norm_num) (Ioi_subset_Ioi (by norm_num)) z
  have h3 : (wndKernelL2 U (Ioi 1) z : ℝ × ℂ → ℝ) =ᵐ[volume] wndKernel U (Ioi 1) z := by
    rw [wndKernelL2, dite_eq_left_of_eq_true (eq_true hmem)]; exact hmem.coeFn_toLp
  have h4 : (kernelU0 U z : ℝ × ℂ → ℝ) =ᵐ[volume] kerIU U (Ioc 0 1) z := by
    rw [kernelU0_eq hU hz]; exact MemLp.coeFn_toLp _
  have h5 : (hatDiffKernel0 z : ℝ × ℂ → ℝ) =ᵐ[volume] kerI (Ioc 0 1) z := by
    rw [hatDiffKernel0]; exact MemLp.coeFn_toLp _
  unfold dgUHatKernel dgA1Kernel
  filter_upwards [Lp.coeFn_sub (wndKernelL2 U (Ioi 1) z + kernelU0 U z) (hatDiffKernel0 z),
    Lp.coeFn_add (wndKernelL2 U (Ioi 1) z) (kernelU0 U z), h3, h4, h5] with p h1 h2 e3 e4 e5
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, e3, e4, e5]
  obtain ⟨s, w⟩ := p
  simp only [wndKernel, kerIU, kerI, hatKer, kerU, kerDiff, indicator, mem_Ioi, mem_Ioc]
  by_cases h0 : 0 < s
  · by_cases h1' : s ≤ 1
    · simp [h0, h1', not_lt.2 h1']
    · simp [h0, h1', lt_of_not_ge h1']
  · simp [h0, show ¬ 1 < s by linarith]

lemma abs_wnd_sub_hatKer_le (U : Set ℂ) (z : ℂ) (p : ℝ × ℂ) :
    |wndKernel U (Ioi 0) z p - hatKer z p| ≤ Real.pi⁻¹ + 2 * hatKer z p := by
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
      have hn := killedHeat_nonneg U (s / 2).toNNReal z w
      rw [ew, eh, abs_le]
      constructor <;> nlinarith [inv_pos.2 hpi]
    · have hm : s ∉ Ioc (0 : ℝ) 1 := fun h => h1 h.2
      have eh : hatKer z (s, w) = 0 := by simp only [hatKer]; rw [indicator_of_notMem hm]
      rw [eh, sub_zero, mul_zero, add_zero, abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
      refine (wndKernel_le U _ z (s, w) h0).trans ?_
      exact inv_anti₀ hpi (le_mul_of_one_le_right hpi.le (by simpa using (not_le.1 h1).le))
  · have hm : s ∉ Ioc (0 : ℝ) 1 := fun h => h0 h.1
    have eh : hatKer z (s, w) = 0 := by simp only [hatKer]; rw [indicator_of_notMem hm]
    have ew : wndKernel U (Ioi 0) z (s, w) = 0 := by simp [wndKernel, h0]
    rw [eh, ew]; simp; positivity

lemma integrable_hatKer_prod (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable (fun q : ℂ × (ℝ × ℂ) => hatKer q.1 q.2) (μ.prod volume) := by
  have hm := measurable_hatKer_uncurry
  have hslice : ∀ z, Integrable (hatKer z) (volume : Measure (ℝ × ℂ)) ∧
      ∫ p, hatKer z p = 1 := by
    intro z
    have hmz : Measurable (hatKer z) := by
      have e : hatKer z = (Prod.fst ⁻¹' Ioc (0 : ℝ) 1).indicator
          (fun p : ℝ × ℂ => heatKernel (p.1 / 2) z p.2) := by
        funext p; simp [hatKer, indicator]
      rw [e]
      refine Measurable.indicator ?_ (measurableSet_Ioc.preimage measurable_fst)
      unfold heatKernel; fun_prop
    have e : ∀ s : ℝ, ∫ w, hatKer z (s, w) = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s := by
      intro s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1
      · simp only [hatKer]; simp_rw [indicator_of_mem hs]
        exact integral_heatKernel _ (by linarith [hs.1]) z
      · simp only [hatKer]; simp_rw [indicator_of_notMem hs]; simp
    have hi : Integrable (hatKer z) (volume : Measure (ℝ × ℂ)) := by
      rw [Measure.volume_eq_prod, integrable_prod_iff hmz.aestronglyMeasurable]
      refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
      · by_cases hs : s ∈ Ioc (0 : ℝ) 1
        · simp only [hatKer]; simp_rw [indicator_of_mem hs]
          exact integrable_heatKernel _ (by linarith [hs.1]) z
        · simp only [hatKer]; simp_rw [indicator_of_notMem hs]; exact integrable_zero _ _ _
      · have e' : (fun s => ∫ w, ‖hatKer z (s, w)‖) =
            (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
          funext s; rw [← e s]; congr 1; funext w
          rw [Real.norm_of_nonneg (hatKer_nonneg _ _)]
        rw [e']
        exact (integrable_indicator_iff measurableSet_Ioc).2
          (integrableOn_const (by simp))
    refine ⟨hi, ?_⟩
    rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hi)]
    simp_rw [e]
    rw [integral_indicator measurableSet_Ioc]; simp
  have e : (fun z => ∫ p, ‖hatKer z p‖) = fun _ => (1 : ℝ) := by
    funext z; rw [← (hslice z).2]; congr 1; funext p
    rw [Real.norm_of_nonneg (hatKer_nonneg _ _)]
  refine (integrable_prod_iff (ν := (volume : Measure (ℝ × ℂ))) hm.aestronglyMeasurable).2
    ⟨Eventually.of_forall fun z => (hslice z).1, ?_⟩
  exact (integrable_const (1 : ℝ)).congr (Eventually.of_forall fun z => (congrFun e z).symm)

/-- the Bochner integral of the kernel of `h^U − ĥ` against `μ` is the kernel of
`(h^U, μ) − (ĥ, μ)` -/
theorem integral_dgUHatKernel_ae_eq {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, Metric.ball z (1 / 10) ⊆ U) (hk : Integrable (dgUHatKernel U) μ) :
    ((∫ z, dgUHatKernel U z ∂μ : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume]
      fun p => measKer U (Ioi 0) μ p - hatMeasKer μ p := by
  have hpi := Real.pi_pos
  set F : ℂ × (ℝ × ℂ) → ℝ := fun q => wndKernel U (Ioi 0) q.1 q.2 - hatKer q.1 q.2 with hF
  have hm1 := measurable_wndKernel_uncurry hU (measurableSet_Ioi (a := (0 : ℝ)))
  have hm2 := measurable_hatKer_uncurry
  have hFm : Measurable F := hm1.sub hm2
  have hpt : ∀ p, ∫ z, F (z, p) ∂μ = measKer U (Ioi 0) μ p - hatMeasKer μ p := by
    intro p
    have i1 : Integrable (fun z => wndKernel U (Ioi 0) z p) μ := by
      by_cases hp : 0 < p.1
      · refine Integrable.of_bound (Measurable.of_uncurry_right hm1).aestronglyMeasurable
          (Real.pi * p.1)⁻¹ (Eventually.of_forall fun z => ?_)
        rw [Real.norm_of_nonneg (wndKernel_nonneg _ _ _ _)]; exact wndKernel_le U _ z p hp
      · have : (fun z => wndKernel U (Ioi 0) z p) = fun _ => 0 := by
          funext z; simp [wndKernel, hp]
        rw [this]; exact integrable_zero _ _ _
    have i2 : Integrable (fun z => hatKer z p) μ := by
      by_cases hp : 0 < p.1
      · refine Integrable.of_bound (Measurable.of_uncurry_right hm2).aestronglyMeasurable
          (Real.pi * p.1)⁻¹ (Eventually.of_forall fun z => ?_)
        rw [Real.norm_of_nonneg (hatKer_nonneg _ _)]; exact hatKer_le z p hp
      · have : (fun z => hatKer z p) = fun _ => 0 := by
          funext z; simp only [hatKer]; rw [indicator_of_notMem (fun h => hp h.1)]
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
    rw [Real.norm_eq_abs]; exact abs_wnd_sub_hatKer_le U q.1 q.2
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun E hE hEf => ?_)
    (fun E hE hEf => ?_) (fun E hE hEf => ?_)
  · have : Fact (volume E < ∞) := ⟨hEf⟩
    exact ((Lp.memLp _).restrict E).integrable one_le_two
  · exact ((hint E hE hEf).integral_prod_right).congr (Eventually.of_forall hpt)
  · rw [← L2.inner_indicatorConstLp_one hE hEf.ne,
      ← integral_inner (𝕜 := ℝ) hk (indicatorConstLp 2 hE hEf.ne (1 : ℝ))]
    simp_rw [L2.inner_indicatorConstLp_one hE hEf.ne]
    have h1 : ∀ᵐ z ∂μ, ∫ p in E, (dgUHatKernel U z : ℝ × ℂ → ℝ) p = ∫ p in E, F (z, p) := by
      filter_upwards [hμ] with z hz
      refine setIntegral_congr_ae hE ?_
      filter_upwards [dgUHatKernel_ae_eq hU hR hUR hz] with p hp _ using hp
    rw [integral_congr_ae h1]
    rw [integral_integral_swap (f := fun z p => F (z, p)) (hint E hE hEf)]
    exact setIntegral_congr_fun hE fun p _ => hpt p

end DG
end LQGMetric
