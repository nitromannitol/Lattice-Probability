/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatScale
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent2Circ
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppAShell
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# DG scale invariance of `ĥ`, part 2: kernel covariance (task P2-DG105c, D105 N5)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`): `ĥ = √π ∫_0^1 ∫ p_{s/2}(·, w)
W(dw, ds)` (DG (3.1), DG:907–917), `ĥ_t = √π ∫_{t²}^1 …` (DG:907), and the scale invariance
DG:1010 ("`(ĥ − ĥ_δ)(δ·+b)` has the same law as `ĥ`") made pathwise (DEC-105 §1 item 3, §2):

* `heatKernel_affineC`: `p_{δ²t}(δx+b, δy+b) = δ⁻² p_t(x, y)` (explicit Gaussian formula).
* `scFun_hatMeasKerI`: the kernel identity `U_{δ,b}(K^I_μ) = K^{δ²I}_{(δ·+b)_*μ}` for the time-cut
  kernels `K^I_μ(s,w) = ∫ 1_I(s) p_{s/2}(y, w) μ(dy)` (change of variables `s = δ²s'`,
  `w = δw' + b`).
* `memLp_hatMeasKerI`: the coarse kernel `K^{(c,1]}_ν` is square integrable for every finite `ν`
  (`ĥ_δ` is a regular field).
* `wnScale_hatMeasKerL2`: `U_{δ,b}(K^{(0,1]}_μ) = K^{(0,1]}_ν − K^{(δ²,1]}_ν`, `ν = (δ·+b)_*μ`.
* **`dgHat_wnScale`**: for `0 < δ ≤ 1`, pathwise a.s.
  `ĥ[W ∘ U_{δ,b}](σ_{z,r}) = ĥ[W](σ_{δz+b, δr}) − ĥ_δ[W](σ_{δz+b, δr})`, i.e. the circle averages of
  `(ĥ − ĥ_δ)(δ·+b)` are those of the `ĥ` of the white noise `W ∘ U_{δ,b}` (`isWhiteNoise_comp`).

Own elementary argument (DG state it as a "basic property of `ĥ`"; DV-D105-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise QuantumZipper KilledHeat DZZ GMCIdent SupTail

/-- the time-cut kernel `1_I(s) p_{s/2}(z, w)` of `ĥ` (`hatKer z = hatKerI (0,1] z`) -/
def hatKerI (I : Set ℝ) (z : ℂ) (p : ℝ × ℂ) : ℝ :=
  I.indicator (fun s => heatKernel (s / 2) z p.2) p.1

/-- the time-cut kernel of `(ĥ, μ)`: `K^I_μ(s, w) = ∫ 1_I(s) p_{s/2}(y, w) μ(dy)` -/
def hatMeasKerI (I : Set ℝ) (μ : Measure ℂ) (p : ℝ × ℂ) : ℝ := ∫ z, hatKerI I z p ∂μ

open Classical in
/-- the `L²` class of `hatMeasKerI I μ` (junk `0` if it is not square integrable) -/
def hatMeasKerIL2 (I : Set ℝ) (μ : Measure ℂ) : WNSpace :=
  if h : MemLp (hatMeasKerI I μ) 2 volume then h.toLp _ else 0

lemma hatMeasKer_eq_I (μ : Measure ℂ) : hatMeasKer μ = hatMeasKerI (Ioc 0 1) μ := rfl

lemma hatKerI_nonneg {I : Set ℝ} (hI : I ⊆ Ioi 0) (z : ℂ) (p : ℝ × ℂ) : 0 ≤ hatKerI I z p := by
  unfold hatKerI
  by_cases h : p.1 ∈ I
  · rw [indicator_of_mem h]; exact heatKernel_nonneg _ (by linarith [mem_Ioi.1 (hI h)]) _ _
  · rw [indicator_of_notMem h]

lemma hatKerI_le {I : Set ℝ} {c : ℝ} (hc : 0 < c) (hI : I ⊆ Ioi c) (z : ℂ) (p : ℝ × ℂ) :
    hatKerI I z p ≤ (Real.pi * c)⁻¹ := by
  unfold hatKerI
  by_cases h : p.1 ∈ I
  · have hp : c < p.1 := hI h
    rw [indicator_of_mem h]
    refine (GFFExist.heatKernel_le _ (by linarith) _ _).trans ?_
    rw [show 2 * Real.pi * (p.1 / 2) = Real.pi * p.1 by ring]
    exact inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos])
  · rw [indicator_of_notMem h]; positivity

lemma measurable_hatKerI_uncurry {I : Set ℝ} (hI : MeasurableSet I) :
    Measurable fun q : (ℝ × ℂ) × ℂ => hatKerI I q.2 q.1 := by
  have e : (fun q : (ℝ × ℂ) × ℂ => hatKerI I q.2 q.1) =
      ({q : (ℝ × ℂ) × ℂ | q.1.1 ∈ I}).indicator (fun q => heatKernel (q.1.1 / 2) q.2 q.1.2) := by
    funext q; simp [hatKerI, indicator]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage (measurable_fst.comp measurable_fst))
  unfold heatKernel; fun_prop

lemma integrable_hatKerI {I : Set ℝ} (hI : I ⊆ Ioi 0) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (p : ℝ × ℂ) : Integrable (fun z => hatKerI I z p) μ := by
  by_cases hp : p.1 ∈ I
  · have hp0 : 0 < p.1 := hI hp
    refine Integrable.of_bound (C := (Real.pi * p.1)⁻¹) ?_ (Eventually.of_forall fun z => ?_)
    · have e : (fun z => hatKerI I z p) = fun z => heatKernel (p.1 / 2) z p.2 := by
        funext z; simp [hatKerI, hp]
      rw [e]; exact (by unfold heatKernel; fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hatKerI_nonneg hI z p)]
      simp only [hatKerI, indicator_of_mem hp]
      refine (GFFExist.heatKernel_le _ (by linarith) _ _).trans (le_of_eq ?_)
      congr 1; ring
  · have : (fun z => hatKerI I z p) = fun _ => 0 := by funext z; simp [hatKerI, hp]
    rw [this]; exact integrable_zero _ _ _

lemma hatMeasKerI_nonneg {I : Set ℝ} (hI : I ⊆ Ioi 0) (μ : Measure ℂ) (p : ℝ × ℂ) :
    0 ≤ hatMeasKerI I μ p :=
  integral_nonneg fun z => hatKerI_nonneg hI z p

/-- the affine map `y ↦ δy + b` as a measurable equivalence -/
def affineEquivC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : ℂ ≃ᵐ ℂ :=
  ((Homeomorph.mulLeft₀ (δ : ℂ) (by exact_mod_cast hδ.ne')).trans
    (Homeomorph.addRight b)).toMeasurableEquiv

lemma coe_affineEquivC {δ : ℝ} (hδ : 0 < δ) (b : ℂ) : ⇑(affineEquivC hδ b) = affineC δ b := rfl

/-- **Kernel covariance**: `U_{δ,b}(K^I_μ) = K^{I'}_{(δ·+b)_*μ}` where `I' = δ² I`. -/
theorem scFun_hatMeasKerI {δ : ℝ} (hδ : 0 < δ) (b : ℂ) {I I' : Set ℝ}
    (hI : ∀ s, s ∈ I' ↔ (δ ^ 2)⁻¹ * s ∈ I) (μ : Measure ℂ) :
    scFun δ b (hatMeasKerI I μ) = hatMeasKerI I' (μ.map (affineC δ b)) := by
  funext p
  have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [← coe_affineEquivC hδ b]
  simp only [scFun, hatMeasKerI]
  rw [integral_map_equiv, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hatKerI, scMap, coe_affineEquivC]
  by_cases hs : p.1 ∈ I'
  · rw [indicator_of_mem hs, indicator_of_mem ((hI _).1 hs)]
    have hw : affineC δ b ((δ⁻¹ : ℝ) • (p.2 - b)) = p.2 := by
      simp only [affineC, Complex.real_smul, Complex.ofReal_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hδC, one_mul, sub_add_cancel]
    rw [← heatKernel_affineC hδ b, hw,
      show δ ^ 2 * ((δ ^ 2)⁻¹ * p.1 / 2) = p.1 / 2 by field_simp]
  · rw [indicator_of_notMem hs, indicator_of_notMem (fun h => hs ((hI _).2 h)), mul_zero]

/-- `K^{(0,d]}_μ = K^{(0,c]}_μ + K^{(c,d]}_μ` (`ĥ = (ĥ − ĥ_{√c}) + ĥ_{√c}` for `d = 1`) -/
lemma hatMeasKerI_split {c d : ℝ} (hc0 : 0 < c) (hcd : c ≤ d) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (p : ℝ × ℂ) :
    hatMeasKerI (Ioc 0 d) μ p = hatMeasKerI (Ioc 0 c) μ p + hatMeasKerI (Ioc c d) μ p := by
  simp only [hatMeasKerI]
  rw [← integral_add (integrable_hatKerI Ioc_subset_Ioi_self μ p)
    (integrable_hatKerI (fun s hs => hc0.trans hs.1) μ p)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hatKerI]
  by_cases h1 : p.1 ∈ Ioc 0 c
  · have h2 : p.1 ∈ Ioc (0 : ℝ) d := ⟨h1.1, h1.2.trans hcd⟩
    have h3 : p.1 ∉ Ioc c d := fun h => absurd h1.2 (not_le.2 h.1)
    rw [indicator_of_mem h2, indicator_of_mem h1, indicator_of_notMem h3, add_zero]
  · by_cases h3 : p.1 ∈ Ioc c d
    · have h2 : p.1 ∈ Ioc (0 : ℝ) d := ⟨hc0.trans h3.1, h3.2⟩
      rw [indicator_of_mem h2, indicator_of_notMem h1, indicator_of_mem h3, zero_add]
    · have h2 : p.1 ∉ Ioc (0 : ℝ) d := fun h => by
        by_cases hc : p.1 ≤ c
        · exact h1 ⟨h.1, hc⟩
        · exact h3 ⟨not_le.1 hc, h.2⟩
      rw [indicator_of_notMem h2, indicator_of_notMem h1, indicator_of_notMem h3, add_zero]

lemma lintegral_hatKerI {I : Set ℝ} (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) (y : ℂ) :
    ∫⁻ p, ENNReal.ofReal (hatKerI I y p) = volume I := by
  have hm : Measurable fun p : ℝ × ℂ => ENNReal.ofReal (hatKerI I y p) :=
    ((measurable_hatKerI_uncurry hI).comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have e : ∀ s : ℝ, ∫⁻ w, ENNReal.ofReal (hatKerI I y (s, w)) = I.indicator 1 s := by
    intro s
    by_cases hs : s ∈ I
    · have hs0 : 0 < s := hI0 hs
      simp only [hatKerI, indicator_of_mem hs, Pi.one_apply]
      exact GFFExist.lintegral_ofReal_heatKernel (by linarith) y
    · simp [hatKerI, hs]
  simp_rw [e]
  rw [lintegral_indicator_one hI]

/-- **The coarse kernel is square integrable**: `K^I_ν ∈ L²` for `I ⊆ (c, d]`, `c > 0`, `ν`
finite (`ĥ_{√c}` is a regular field). -/
theorem memLp_hatMeasKerI {I : Set ℝ} (hI : MeasurableSet I) {c d : ℝ} (hc : 0 < c)
    (hIc : I ⊆ Ioc c d) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    MemLp (hatMeasKerI I ν) 2 volume := by
  have hIc' : I ⊆ Ioi c := fun s hs => (hIc hs).1
  have hI0 : I ⊆ Ioi 0 := fun s hs => hc.trans (hIc hs).1
  set f := hatMeasKerI I ν
  set M := (Real.pi * c)⁻¹ * ν.real univ
  have hM : 0 ≤ M := by positivity
  have hnn : ∀ p, 0 ≤ f p := hatMeasKerI_nonneg hI0 ν
  have hle : ∀ p, f p ≤ M := fun p => by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => hatKerI I z p)
      (C := (Real.pi * c)⁻¹) (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hatKerI_nonneg hI0 z p)]
        exact hatKerI_le hc hIc' z p)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self (f p)).trans h
  have hfm : Measurable f :=
    (measurable_hatKerI_uncurry hI).stronglyMeasurable.integral_prod_right'.measurable
  have hof : ∀ p, ENNReal.ofReal (f p) = ∫⁻ y, ENNReal.ofReal (hatKerI I y p) ∂ν := fun p =>
    ofReal_integral_eq_lintegral_ofReal (integrable_hatKerI hI0 ν p)
      (Eventually.of_forall fun y => hatKerI_nonneg hI0 y p)
  have hint : ∫⁻ p, ENNReal.ofReal (f p) < ∞ := by
    simp_rw [hof]
    rw [lintegral_lintegral_swap (measurable_hatKerI_uncurry hI).ennreal_ofReal.aemeasurable]
    simp_rw [lintegral_hatKerI hI hI0]
    rw [lintegral_const]
    refine ENNReal.mul_lt_top ((measure_mono hIc).trans_lt ?_) (measure_lt_top _ _)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  rw [memLp_two_iff_integrable_sq hfm.aestronglyMeasurable]
  refine ⟨(hfm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => sq_nonneg _)]
  calc ∫⁻ p, ENNReal.ofReal (f p ^ 2)
      ≤ ∫⁻ p, ENNReal.ofReal M * ENNReal.ofReal (f p) := lintegral_mono fun p => by
        rw [← ENNReal.ofReal_mul hM]
        exact ENNReal.ofReal_le_ofReal (by rw [sq]; exact mul_le_mul_of_nonneg_right (hle p) (hnn p))
    _ = ENNReal.ofReal M * ∫⁻ p, ENNReal.ofReal (f p) := lintegral_const_mul _ hfm.ennreal_ofReal
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

/-- **`L²` kernel identity**: `U_{δ,b}(K^{(0,1]}_μ) = K^{(0,1]}_ν − K^{(δ²,1]}_ν`,
`ν = (δ·+b)_*μ`, `0 < δ ≤ 1`. -/
theorem wnScale_hatMeasKerL2 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b : ℂ) (μ : Measure ℂ)
    [IsFiniteMeasure μ] (hμ : MemLp (hatMeasKer μ) 2 volume) :
    wnScale hδ b (hatMeasKerL2 μ) = hatMeasKerL2 (μ.map (affineC δ b)) -
      hatMeasKerIL2 (Ioc (δ ^ 2) 1) (μ.map (affineC δ b)) := by
  set ν := μ.map (affineC δ b)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδ21 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hlow : scFun δ b (hatMeasKer μ) = hatMeasKerI (Ioc 0 (δ ^ 2)) ν :=
    scFun_hatMeasKerI hδ b (mem_Ioc_iff_scale hδ) μ
  have hmlow : MemLp (hatMeasKerI (Ioc 0 (δ ^ 2)) ν) 2 volume := hlow ▸ memLp_scFun hδ b hμ
  have hmhigh : MemLp (hatMeasKerI (Ioc (δ ^ 2) 1) ν) 2 volume :=
    memLp_hatMeasKerI measurableSet_Ioc hδ2 subset_rfl ν
  have hsplit : hatMeasKer ν = hatMeasKerI (Ioc 0 (δ ^ 2)) ν + hatMeasKerI (Ioc (δ ^ 2) 1) ν :=
    funext fun p => hatMeasKerI_split hδ2 hδ21 ν p
  have hmfull : MemLp (hatMeasKer ν) 2 volume := hsplit ▸ hmlow.add hmhigh
  simp only [hatMeasKerL2, hatMeasKerIL2, dite_eq_left_of_eq_true (eq_true hμ), dite_eq_left_of_eq_true (eq_true hmfull),
    dite_eq_left_of_eq_true (eq_true hmhigh)]
  rw [wnScale_toLp, ← MemLp.toLp_sub]
  refine MemLp.toLp_congr _ _ (Eventually.of_forall fun p => ?_)
  rw [hlow, hsplit, Pi.sub_apply, Pi.add_apply, add_sub_cancel_right]

/-- `K^{(0,1]}_μ ∈ L²` is preserved by every affine image `y ↦ δy + b`, `δ > 0`. -/
theorem memLp_hatMeasKer_map {δ : ℝ} (hδ : 0 < δ) (b : ℂ) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : MemLp (hatMeasKer μ) 2 volume) :
    MemLp (hatMeasKer (μ.map (affineC δ b))) 2 volume := by
  set ν := μ.map (affineC δ b)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hmlow : MemLp (hatMeasKerI (Ioc 0 (δ ^ 2)) ν) 2 volume :=
    scFun_hatMeasKerI hδ b (mem_Ioc_iff_scale hδ) μ ▸ memLp_scFun hδ b hμ
  rcases le_or_gt (δ ^ 2) 1 with h1 | h1
  · have e : hatMeasKer ν = hatMeasKerI (Ioc 0 (δ ^ 2)) ν + hatMeasKerI (Ioc (δ ^ 2) 1) ν :=
      funext fun p => hatMeasKerI_split hδ2 h1 ν p
    exact e ▸ hmlow.add (memLp_hatMeasKerI measurableSet_Ioc hδ2 subset_rfl ν)
  · have e : hatMeasKer ν = hatMeasKerI (Ioc 0 (δ ^ 2)) ν - hatMeasKerI (Ioc 1 (δ ^ 2)) ν :=
      funext fun p => by
        have := hatMeasKerI_split one_pos h1.le ν p
        rw [Pi.sub_apply, hatMeasKer_eq_I]; linarith
    exact e ▸ hmlow.sub (memLp_hatMeasKerI measurableSet_Ioc one_pos subset_rfl ν)

/-- `K^{(0,1]}_{σ_{z,r}} ∈ L²` for circles in a box with `B(x,1/10) ⊆ 𝕍` (from the kernel identity
of `h^𝕍 − ĥ`, `integral_dgUHatKernel_ae_eq`; extracted from the proof of
`dg_lemma31_hU_hat_circ`). -/
lemma memLp_hatMeasKer_circle_box {y : ℂ} {b : ℝ} (hb : 0 < b)
    (hK : ∀ z ∈ ferniqueBox y b, Metric.ball z (1 / 10) ⊆ openSquare) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hB : Metric.closedBall z r ⊆ ferniqueBox y b) :
    MemLp (hatMeasKer (circleUnif z r)) 2 volume := by
  set S := ferniqueBox y b
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  set σ := circleUnif z r
  set k := dgUHatKernel openSquare
  have hσS : σ Sᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 hB) (circleUnif_compl_closedBall hr z)
  have hSae : ∀ᵐ x ∂σ, x ∈ S := mem_ae_iff.2 hσS
  obtain ⟨L, hL0, hL⟩ := dgUHatKernel_holder isOpen_openSquare isBounded_openSquare hb hK
  have hkc : ContinuousOn k S := continuousOn_of_sq_le hL0 hL
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hkc
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hkm : AEStronglyMeasurable k σ := by
    have := hkc.aestronglyMeasurable (μ := σ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem hSae] at this
  have hki : Integrable k σ := Integrable.of_bound hkm M (hSae.mono fun x hx => hM x hx)
  have hBsq : Metric.closedBall z r ⊆ openSquare := fun x hx =>
    (hK x (hB hx)) (Metric.mem_ball_self (by norm_num))
  have hm1 := GMCIdent2.memLp_measKer_circle hr hBsq
  have hI := integral_dgUHatKernel_ae_eq isOpen_openSquare (le_of_lt two_pos)
    DZZ.openSquare_subset_ball σ (hSae.mono fun x hx => hK x hx) hki
  refine (hm1.sub (Lp.memLp (∫ x, k x ∂σ))).ae_eq ?_
  filter_upwards [hI] with p hp
  rw [Pi.sub_apply, hp]; ring

/-- **`K^{(0,1]}_{σ_{z,r}} ∈ L²` for every circle** (`r > 0`): the circle of radius `1/20` about
`1/2 + i/2` (`memLp_hatMeasKer_circle_box`) moved by an affine map (`memLp_hatMeasKer_map`). -/
theorem memLp_hatMeasKer_circleUnif (z : ℂ) {r : ℝ} (hr : 0 < r) :
    MemLp (hatMeasKer (circleUnif z r)) 2 volume := by
  set c₀ : ℂ := ⟨1 / 2, 1 / 2⟩
  have hK : ∀ x ∈ ferniqueBox ⟨2 / 5, 2 / 5⟩ (1 / 5), Metric.ball x (1 / 10) ⊆ openSquare := by
    intro x hx w hw
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc] at hx
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := abs_le.1 ((Complex.abs_re_le_norm (w - x)).trans hw.le)
    have h2 := abs_le.1 ((Complex.abs_im_le_norm (w - x)).trans hw.le)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2]
  have hB : Metric.closedBall c₀ (1 / 20) ⊆ ferniqueBox ⟨2 / 5, 2 / 5⟩ (1 / 5) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 := abs_le.1 ((Complex.abs_re_le_norm (w - c₀)).trans hw)
    have h2 := abs_le.1 ((Complex.abs_im_le_norm (w - c₀)).trans hw)
    simp only [Complex.sub_re, Complex.sub_im, c₀] at h1 h2
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have h0 := memLp_hatMeasKer_circle_box (by norm_num) hK (by norm_num) hB
  have h := memLp_hatMeasKer_map (δ := r / (1 / 20)) (by positivity)
    (z - ((r / (1 / 20) : ℝ) : ℂ) * c₀) _ h0
  rwa [map_affineC_circleUnif, show affineC (r / (1 / 20)) (z - ((r / (1 / 20) : ℝ) : ℂ) * c₀) c₀ = z
    by simp only [affineC]; ring, show r / (1 / 20) * (1 / 20) = r by field_simp] at h

/-- `ĥ_δ` tested against `σ_{z,r}`: `√π W(K^{(δ²,1]}_{σ_{z,r}})` (DG:907) -/
def dgHatCoarse {Ω : Type*} (W : WNSpace → Ω → ℝ) (δ : ℝ) (z : ℂ) (r : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (hatMeasKerIL2 (Ioc (δ ^ 2) 1) (circleUnif z r)) ω

/-- **Scale invariance of `ĥ`, pathwise (D105 N5; DG:1010)**: for `0 < δ ≤ 1`, a.s.
`ĥ[W ∘ U_{δ,b}](σ_{z,r}) = ĥ[W](σ_{δz+b, δr}) − ĥ_δ[W](σ_{δz+b, δr})`: the circle averages of
`(ĥ − ĥ_δ)(δ·+b)` are those of the `ĥ` of the white noise `W ∘ U_{δ,b}`. -/
theorem dgHat_wnScale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b z : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun ω => dgHat (fun f ω => W (wnScale hδ b f) ω) z r ω) =ᵐ[P]
      fun ω => dgHat W (affineC δ b z) (δ * r) ω - dgHatCoarse W δ (affineC δ b z) (δ * r) ω := by
  have e := wnScale_hatMeasKerL2 hδ hδ1 b (circleUnif z r) (memLp_hatMeasKer_circleUnif z hr)
  rw [map_affineC_circleUnif] at e
  set f := hatMeasKerL2 (circleUnif (affineC δ b z) (δ * r))
  set g := hatMeasKerIL2 (Ioc (δ ^ 2) 1) (circleUnif (affineC δ b z) (δ * r))
  filter_upwards [hW.add_ae f (-g), hW.smul_ae (-1) g] with ω h1 h2
  rw [neg_one_smul] at h2
  simp only [dgHat, dgHatCoarse]
  rw [e, sub_eq_add_neg, h1, h2]
  ring

/-- `ĥ^tr`'s kernel is dominated by `ĥ`'s (`p_{B} ≤ p`) -/
lemma trMeasKer_le_hatMeasKer (μ : Measure ℂ) [IsFiniteMeasure μ] (p : ℝ × ℂ) :
    trMeasKer μ p ≤ hatMeasKer μ p := by
  have hle : ∀ z, trKer z p ≤ hatKer z p := fun z => by
    simp only [trKer, wndKernel, hatKer]
    by_cases h : p.1 ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem h, indicator_of_mem h]
      refine (killedHeat_le_heatKernel _ _ _ _).trans (le_of_eq ?_)
      rw [Real.coe_toNNReal _ (by linarith [h.1])]
    · rw [indicator_of_notMem h, indicator_of_notMem h]
  have hm : Measurable fun z => trKer z p :=
    by
    have h : Measurable ((fun q : ℂ × (ℝ × ℂ) => trKer q.1 q.2) ∘ fun z : ℂ => (z, p)) :=
      measurable_trKer_uncurry.comp (measurable_id.prodMk measurable_const)
    exact h
  have hi : Integrable (fun z => hatKer z p) μ := integrable_hatKerI Ioc_subset_Ioi_self μ p
  have hi' : Integrable (fun z => trKer z p) μ := by
    refine hi.mono hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ trKer z p from
      wndKernel_nonneg _ _ _ _), abs_of_nonneg (hatKer_nonneg z p)]
    exact hle z
  show ∫ z, trKer z p ∂μ ≤ ∫ z, hatKer z p ∂μ
  exact integral_mono hi' hi hle

/-- `K^{tr}_{σ_{z,r}} ∈ L²` for every circle (`r > 0`) -/
theorem memLp_trMeasKer_circleUnif (z : ℂ) {r : ℝ} (hr : 0 < r) :
    MemLp (trMeasKer (circleUnif z r)) 2 volume := by
  refine (memLp_hatMeasKer_circleUnif z hr).mono
    (measurable_trKer_uncurry.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have h0 : 0 ≤ trMeasKer (circleUnif z r) p := integral_nonneg fun _ => wndKernel_nonneg _ _ _ _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (h0.trans
    (trMeasKer_le_hatMeasKer _ p))]
  exact trMeasKer_le_hatMeasKer _ p

/-- **D105 N5 (dyadic form)**: for `δ = 2^{-m}`, `W ∘ U_{δ,b}` is a white noise and, a.s., its
`ĥ` circle averages are those of `(ĥ − ĥ_δ)(δ·+b)`. -/
theorem dgN5_wnScaleDy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (m : ℕ) (b : ℂ) :
    IsWhiteNoise P (fun f ω => W (wnScaleDy m b f) ω) ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r →
        (fun ω => dgHat (fun f ω => W (wnScaleDy m b f) ω) z r ω) =ᵐ[P] fun ω =>
          dgHat W (affineC (2⁻¹ ^ m) b z) (2⁻¹ ^ m * r) ω -
            dgHatCoarse W (2⁻¹ ^ m) (affineC (2⁻¹ ^ m) b z) (2⁻¹ ^ m * r) ω :=
  ⟨isWhiteNoise_comp hW _, fun z _ hr =>
    dgHat_wnScale hW _ (pow_le_one₀ (by norm_num) (by norm_num)) b z hr⟩

end DG
end LQGMetric
