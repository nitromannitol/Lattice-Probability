/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen7 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Parseval for the sine modes of the square (task P2-KHSQ2, G4)

For `f ∈ C_c^∞((a,a+L)²)` and `σ` bounded measurable vanishing off the square:

  `∑_p (4/L²) f̂_p σ̂_p = ∫ f σ`   (`HeatSq.hasSum_sqCoef_parseval`).

Proof (the heat-kernel route of the handoff P2-KHSQ): by the spectral form
`HeatSq.hasSum_integral_sqDirKernel`, `∑_p (4/L²) e^{−λ_p s/2} σ̂_p f̂_p = ∫∫ σ(x) p^D_s(x,y) f(y)`.
As `s = c⁻² → 0`, the left side tends to `∑ (4/L²) σ̂ f̂` (dominated convergence for series,
mathlib `tendsto_tsum_of_dominated_convergence`), and the right side tends to `∫ σ f`: on the
support of `f` the square kernel differs from the planar heat kernel by `O(p_s(d,0)) → 0`
(`HeatSq.abs_sqDirKernel_sub_le`), and the planar heat kernel is an approximate identity
(mathlib `tendsto_integral_comp_smul_smul_of_integrable'`). This is the completeness of the
Dirichlet eigenfunctions of the square deduced from `p^D_s → δ`; standard (e.g. Davies,
*Heat kernels and spectral theory*, §1.6), own assembly of the cited pieces.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology Bornology QuantumZipper

namespace LQGMetric
namespace HeatSq

lemma tendsto_cobounded_sq_mul_heatKernel :
    Tendsto (fun x : ℂ => ‖x‖ ^ Module.finrank ℝ ℂ * heatKernel 1 0 x) (cobounded ℂ) (𝓝 0) := by
  rw [Complex.finrank_real_complex]
  have h1 : Tendsto (fun x : ℂ => ‖x‖ ^ 2 / 2) (cobounded ℂ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop).atTop_div_const two_pos
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul (2 * (2 * π)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply, heatKernel, zero_sub, norm_neg, pow_one]
  rw [show -‖x‖ ^ 2 / (2 * 1) = -(‖x‖ ^ 2 / 2) by ring]
  ring

/-- the planar heat kernel is an approximate identity: `∫ p_{c⁻²}(x₀,y) f(y) dy → f(x₀)` -/
lemma tendsto_integral_heatKernel_mul {f : ℂ → ℝ} (hfc : Continuous f) (hfi : Integrable f)
    (x₀ : ℂ) :
    Tendsto (fun c : ℝ => ∫ y, heatKernel (c ^ 2)⁻¹ x₀ y * f y) atTop (𝓝 (f x₀)) := by
  have h := tendsto_integral_comp_smul_smul_of_integrable' (μ := (volume : Measure ℂ))
    (φ := heatKernel 1 0) (fun x => heatKernel_nonneg 1 zero_le_one 0 x)
    (integral_heatKernel 1 one_pos 0) tendsto_cobounded_sq_mul_heatKernel hfi
    hfc.continuousAt (x₀ := x₀)
  refine h.congr' ((eventually_gt_atTop 0).mono fun c hc => integral_congr_ae
    (Eventually.of_forall fun y => ?_))
  simp only [Complex.finrank_real_complex, smul_eq_mul, heatKernel, zero_sub, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hc2 : c ^ 2 ≠ 0 := by positivity
  have e : -(c * ‖x₀ - y‖) ^ 2 / (2 * 1) = -‖x₀ - y‖ ^ 2 / (2 * (c ^ 2)⁻¹) := by
    field_simp
  rw [e]
  field_simp

lemma tendsto_inv_sq_atTop : Tendsto (fun c : ℝ => (c ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)

lemma tendsto_heatKernel_d {d : ℝ} (hd : 0 < d) :
    Tendsto (fun c : ℝ => heatKernel (c ^ 2)⁻¹ (d : ℂ) 0) atTop (𝓝 0) := by
  have h1 : Tendsto (fun c : ℝ => d ^ 2 / 2 * c ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop (by positivity)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul
    ((2 * π)⁻¹ * (2 / d ^ 2))
  rw [mul_zero] at h2
  refine h2.congr' ((eventually_ne_atTop 0).mono fun c hc => ?_)
  simp only [Function.comp_apply, heatKernel, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, pow_one]
  have hd2 : d ^ 2 ≠ 0 := by positivity
  rw [show -d ^ 2 / (2 * (c ^ 2)⁻¹) = -(d ^ 2 / 2 * c ^ 2) by field_simp]
  field_simp

lemma measurable_sqDirKernel_right' {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (x : ℂ) :
    Measurable fun y => sqDirKernel a L s x y := by
  unfold sqDirKernel
  exact (measurable_intervalDirKernel (f := fun _ : ℂ => x.re) (g := fun y : ℂ => y.re) hs hL
    measurable_const Complex.measurable_re).mul
    (measurable_intervalDirKernel (f := fun _ : ℂ => x.im) (g := fun y : ℂ => y.im) hs hL
      measurable_const Complex.measurable_im)

/-- a compact subset of the open square stays at positive distance from its sides -/
lemma exists_margin {a L : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ sqOpen a L) :
    ∃ d > 0, ∀ y ∈ K, y.re ∈ Icc (a + d) (a + L - d) ∧ y.im ∈ Icc (a + d) (a + L - d) := by
  set m : ℂ → ℝ := fun y => min (min (y.re - a) (a + L - y.re)) (min (y.im - a) (a + L - y.im))
  have hm : Continuous m := by fun_prop
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, fun y hy => by simp [hE] at hy⟩
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hm.continuousOn
  obtain ⟨h1, h2, h3, h4⟩ := hKU hy₀
  refine ⟨m y₀, ?_, fun y hy => ?_⟩
  · simp only [m, lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · have := hmin hy
    simp only [mem_ofPred_eq, m, le_min_iff] at this
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := this
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [min_le_left (min (y₀.re - a) (a + L - y₀.re)) (min (y₀.im - a) (a + L - y₀.im)),
        min_le_left (y₀.re - a) (a + L - y₀.re)]
    · linarith [min_le_left (min (y₀.re - a) (a + L - y₀.re)) (min (y₀.im - a) (a + L - y₀.im)),
        min_le_left (y₀.re - a) (a + L - y₀.re)]
    · linarith [min_le_left (min (y₀.re - a) (a + L - y₀.re)) (min (y₀.im - a) (a + L - y₀.im)),
        min_le_left (y₀.re - a) (a + L - y₀.re)]
    · linarith [min_le_left (min (y₀.re - a) (a + L - y₀.re)) (min (y₀.im - a) (a + L - y₀.im)),
        min_le_left (y₀.re - a) (a + L - y₀.re)]

/-- pointwise: `∫ p^D_{c⁻²}(x,y) f(y) dy → f(x)` for `x` in the closed square -/
lemma tendsto_integral_sqDirKernel_mul {a L : ℝ} (hL : 0 < L) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) {x : ℂ} (hxre : x.re ∈ Icc a (a + L))
    (hxim : x.im ∈ Icc a (a + L)) :
    Tendsto (fun c : ℝ => ∫ y, sqDirKernel a L (c ^ 2)⁻¹ x y * f y) atTop (𝓝 (f x)) := by
  have hfc : Continuous f := hf.1.continuous
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hf.2.1
  obtain ⟨Cf, hCf⟩ := hf.2.1.exists_bound_of_continuous hfc
  obtain ⟨d, hd, hdK⟩ := exists_margin hf.2.1.isCompact hf.2.2
  set Kc := 4 * imgConst d L + 4 * imgConst d L ^ 2
  have hlim1 := (tendsto_heatKernel_d hd).const_mul (Kc * ∫ y, |f y|)
  rw [mul_zero] at hlim1
  have key : ∀ᶠ c : ℝ in atTop, ∫ y, sqDirKernel a L (c ^ 2)⁻¹ x y * f y =
      (∫ y, (sqDirKernel a L (c ^ 2)⁻¹ x y - heatKernel (c ^ 2)⁻¹ x y) * f y) +
        ∫ y, heatKernel (c ^ 2)⁻¹ x y * f y ∧
      |∫ y, (sqDirKernel a L (c ^ 2)⁻¹ x y - heatKernel (c ^ 2)⁻¹ x y) * f y| ≤
        Kc * ∫ y, |f y| * heatKernel (c ^ 2)⁻¹ (d : ℂ) 0 := by
    filter_upwards [eventually_ge_atTop 1] with c hc
    have hs : 0 < (c ^ 2)⁻¹ := by positivity
    have hs1 : (c ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc)
    have hb : ∀ y, |(sqDirKernel a L (c ^ 2)⁻¹ x y - heatKernel (c ^ 2)⁻¹ x y) * f y| ≤
        Kc * heatKernel (c ^ 2)⁻¹ (d : ℂ) 0 * |f y| := fun y => by
      rw [abs_mul]
      by_cases hy : y ∈ tsupport f
      · exact mul_le_mul_of_nonneg_right (abs_sqDirKernel_sub_le hs hs1 hd hL hxre hxim
          (hdK y hy).1 (hdK y hy).2) (abs_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero, mul_zero, mul_zero]
    have hpc : Continuous (heatKernel (c ^ 2)⁻¹ x) := by unfold heatKernel; fun_prop
    have hm1 : Measurable fun y => sqDirKernel a L (c ^ 2)⁻¹ x y :=
      measurable_sqDirKernel_right' hs hL x
    have hp : Integrable fun y => heatKernel (c ^ 2)⁻¹ x y * f y :=
      ((integrable_heatKernel _ hs x).mul_const Cf).mono'
        (hpc.mul hfc).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ hs.le x y)]
          exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _ ▸ hCf y)) (heatKernel_nonneg _ hs.le x y))
    have hq : Integrable fun y =>
        (sqDirKernel a L (c ^ 2)⁻¹ x y - heatKernel (c ^ 2)⁻¹ x y) * f y :=
      (hfi.abs.const_mul (Kc * heatKernel (c ^ 2)⁻¹ (d : ℂ) 0)).mono'
        ((hm1.sub hpc.measurable).mul hfc.measurable).aestronglyMeasurable
        (Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hb y))
    refine ⟨?_, ?_⟩
    · rw [← integral_add hq hp]; congr 1; funext y; ring
    · refine (abs_integral_le_integral_abs).trans ((integral_mono hq.abs
        (hfi.abs.const_mul _) hb).trans_eq ?_)
      rw [integral_const_mul, integral_mul_const]; ring
  have hA : Tendsto (fun c : ℝ =>
      ∫ y, (sqDirKernel a L (c ^ 2)⁻¹ x y - heatKernel (c ^ 2)⁻¹ x y) * f y) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ((key.mono fun c hc => (Real.norm_eq_abs _).trans_le hc.2)) ?_
    refine hlim1.congr fun c => ?_
    rw [integral_mul_const]; ring
  have hB := tendsto_integral_heatKernel_mul hfc hfi x
  have := hA.add hB
  rw [zero_add] at this
  exact this.congr' (key.mono fun c hc => hc.1.symm)

lemma sqDecay_le_one {L s : ℝ} (hs : 0 ≤ s) (p : ℕ × ℕ) : sqDecay L s p ≤ 1 := by
  rw [sqDecay_eq, Real.exp_le_one_iff]
  have : 0 ≤ sqRate L p := by unfold sqRate; positivity
  nlinarith

lemma tendsto_sqDecay (L : ℝ) (p : ℕ × ℕ) :
    Tendsto (fun c : ℝ => sqDecay L (c ^ 2)⁻¹ p) atTop (𝓝 1) := by
  simp_rw [sqDecay_eq]
  have hc : Continuous (fun s : ℝ => Real.exp (-sqRate L p * s)) := by fun_prop
  have h := hc.tendsto 0
  simp only [mul_zero, Real.exp_zero] at h
  exact h.comp tendsto_inv_sq_atTop

/-- **G4 (Parseval).** For `f ∈ C_c^∞(U)` and `σ` bounded measurable vanishing off the square,
`∑_p (4/L²) f̂_p σ̂_p = ∫ f σ`. -/
theorem hasSum_sqCoef_parseval {a L : ℝ} (hL : 0 < L) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) :
    HasSum (fun p => 4 / L ^ 2 * (sqCoef a L f p * sqCoef a L σ p)) (∫ z, f z * σ z) := by
  have hfc : Continuous f := hf.1.continuous
  obtain ⟨Cf, hCf⟩ := hf.2.1.exists_bound_of_continuous hfc
  have hCf' : ∀ z, |f z| ≤ Cf := fun z => (Real.norm_eq_abs _).symm.trans_le (hCf z)
  have hf0 : ∀ z ∉ sqOpen a L, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hf.2.2 h)
  have hfi := integrable_of_bdd_sq (a := a) (L := L) hfc.measurable hCf' hf0
  have hσi := integrable_of_bdd_sq hσm hC h0
  have habs : Summable fun p => |sqCoef a L σ p * sqCoef a L f p| :=
    ((summable_sqCoef_sq hL hσm hC h0).add (summable_sqCoef_sq hL hfc.measurable hCf' hf0)).of_nonneg_of_le
      (fun p => abs_nonneg _) (fun p => abs_mul_le_sq_add_sq _ _)
  have hsum : Summable fun p => 4 / L ^ 2 * (sqCoef a L σ p * sqCoef a L f p) :=
    (habs.mul_left (4 / L ^ 2)).of_norm_bounded (fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 / L ^ 2)])
  set T : ℝ → ℝ := fun c => ∫ x, ∫ y, σ x * sqDirKernel a L (c ^ 2)⁻¹ x y * f y
  -- the series side
  have hT1 : Tendsto T atTop (𝓝 (∑' p, 4 / L ^ 2 * (sqCoef a L σ p * sqCoef a L f p))) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (c : ℝ) p => 4 / L ^ 2 * sqDecay L (c ^ 2)⁻¹ p * (sqCoef a L σ p * sqCoef a L f p))
      (g := fun p => 4 / L ^ 2 * (sqCoef a L σ p * sqCoef a L f p))
      (habs.mul_left (4 / L ^ 2)) (fun p => ?_) (Eventually.of_forall fun c p => ?_)
    · refine h.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
      exact (hasSum_integral_sqDirKernel (by positivity) hL hσi hfi).tsum_eq
    · have := ((tendsto_sqDecay L p).const_mul (4 / L ^ 2)).mul_const
        (sqCoef a L σ p * sqCoef a L f p)
      simpa using this
    · have h1 := sqDecay_le_one (L := L) (inv_nonneg.2 (sq_nonneg c)) p
      have h2 := sqDecay_pos L (c ^ 2)⁻¹ p
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 / L ^ 2),
        abs_of_pos h2]
      calc 4 / L ^ 2 * sqDecay L (c ^ 2)⁻¹ p * |sqCoef a L σ p * sqCoef a L f p|
          ≤ 4 / L ^ 2 * 1 * |sqCoef a L σ p * sqCoef a L f p| := by gcongr
        _ = _ := by ring
  -- the kernel side
  have hT2 : Tendsto T atTop (𝓝 (∫ x, σ x * f x)) := by
    have e : ∀ c, T c = ∫ x, σ x * ∫ y, sqDirKernel a L (c ^ 2)⁻¹ x y * f y := fun c => by
      show ∫ x, ∫ y, _ = _
      congr 1; funext x; rw [← integral_const_mul]; congr 1; funext y; ring
    rw [show T = fun c => ∫ x, σ x * ∫ y, sqDirKernel a L (c ^ 2)⁻¹ x y * f y from funext e]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => |σ x| * (4 * Cf))
      ((eventually_gt_atTop 0).mono fun c hc => ?_)
      ((eventually_gt_atTop 0).mono fun c hc => Eventually.of_forall fun x => ?_)
      (hσi.abs.mul_const _) (Eventually.of_forall fun x => ?_)
    · have hs : 0 < (c ^ 2)⁻¹ := by positivity
      have hF : StronglyMeasurable fun q : ℂ × ℂ => sqDirKernel a L (c ^ 2)⁻¹ q.1 q.2 * f q.2 :=
        ((measurable_sqDirKernel hs hL).mul (hfc.measurable.comp measurable_snd)).stronglyMeasurable
      exact hσm.aestronglyMeasurable.mul hF.integral_prod_right'.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_integral_sqDirKernel_mul_le (by positivity) hL hCf' hf0 x)
        (abs_nonneg _)
    · by_cases hx : x ∈ sqOpen a L
      · obtain ⟨h1, h2, h3, h4⟩ := hx
        exact (tendsto_integral_sqDirKernel_mul hL hf ⟨h1.le, h2.le⟩ ⟨h3.le, h4.le⟩).const_mul _
      · simp only [h0 x hx, zero_mul]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hT1 hT2
  have := hsum.hasSum
  have e2 : ∫ x, σ x * f x = ∫ z, f z * σ z :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [heq, e2] at this
  exact this.congr_fun fun p => by ring

end HeatSq
end LQGMetric
