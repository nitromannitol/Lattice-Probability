/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenSquareMem at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: MemLp is now the bound eLpNorm < ∞ (measurability via MemLp.aestronglyMeasurable).
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquareCut
import Mathlib.MeasureTheory.Function.UniformIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`HeatSq.gradFeat_sqMode_mem_gradClosure`: `g_p = gradFeat U φ_p` lies in the closure of the
gradient features of `C_c^∞(U)`, `U = (a,a+L)²`. Approximants:
`f_δ(z) = χ_δ(x) sin_j(x) · χ_δ(y) sin_k(y)` with the cutoff `HeatSq.cutoff` (`δ = 1/(n+1)`):
they lie in `C_c^∞(U)`, their gradients are bounded uniformly in `δ`
(`HeatSq.abs_cutoffD_mul_sinMode_le`) and agree with `∇φ_p` near each point of `U` once `δ` is
small; Vitali's theorem (mathlib `tendsto_Lp_finite_of_tendsto_ae`, as in QZ
`K3.exists_radialApprox_tendsto`) gives `L²` convergence. Standard (every Lipschitz function
vanishing on `∂U` is in `H¹₀(U)`; Evans, *PDE*, §5.5, Thm 2); own elementary implementation.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology QuantumZipper QuantumZipper.K3
open scoped ENNReal NNReal

namespace LQGMetric
namespace HeatSq

/-- the cut-off sine mode `χ_δ sin_k` -/
def cutMode (a L δ : ℝ) (k : ℕ) (u : ℝ) : ℝ := cutoff a L δ u * sinMode a L k u

/-- its derivative -/
def cutModeD (a L δ : ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  cutoffD a L δ u * sinMode a L k u + cutoff a L δ u * (π * k / L * cosMode a L k u)

lemma hasDerivAt_cutMode (a L δ : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (cutMode a L δ k) (cutModeD a L δ k u) u :=
  ((hasDerivAt_cutoff a L δ u).mul (hasDerivAt_sinMode a L k u)).congr_deriv
    (by unfold cutModeD; ring)

lemma abs_cutMode_le (a L δ : ℝ) (k : ℕ) (u : ℝ) : |cutMode a L δ k u| ≤ 1 := by
  unfold cutMode
  rw [abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _ _)]
  exact mul_le_one₀ (cutoff_le_one _ _ _ _) (abs_nonneg _) (abs_sinMode_le _ _ _ _)

lemma abs_cutModeD_le {a L δ M : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hM : ∀ t, |deriv Real.smoothTransition t| * (|t| + 1) ≤ M) (k : ℕ) (u : ℝ) :
    |cutModeD a L δ k u| ≤ (2 * M + 1) * (π * k / L) := by
  unfold cutModeD
  have h1 := abs_cutoffD_mul_sinMode_le (a := a) hL hδ hM k u
  have hc : 0 ≤ π * k / L := by positivity
  have h2 : |cutoff a L δ u * (π * k / L * cosMode a L k u)| ≤ π * k / L := by
    rw [abs_mul, abs_mul, abs_of_nonneg (cutoff_nonneg _ _ _ _), abs_of_nonneg hc]
    calc cutoff a L δ u * (π * k / L * |cosMode a L k u|) ≤ 1 * (π * k / L * 1) := by
          gcongr
          · exact cutoff_le_one _ _ _ _
          · exact abs_cos_le_one _
      _ = _ := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * (π * k / L) * M + π * k / L := add_le_add h1 h2
    _ = _ := by ring

/-- the approximants `f_δ` -/
def sqCut (a L δ : ℝ) (p : ℕ × ℕ) (z : ℂ) : ℝ := cutMode a L δ p.1 z.re * cutMode a L δ p.2 z.im

lemma sqCut_eq_zero {a L δ : ℝ} (hδ : 0 < δ) (p : ℕ × ℕ) {z : ℂ}
    (hz : z ∉ Complex.re ⁻¹' Icc (a + δ) (a + L - δ) ∩ Complex.im ⁻¹' Icc (a + δ) (a + L - δ)) :
    sqCut a L δ p z = 0 := by
  simp only [mem_inter_iff, mem_preimage, mem_Icc, not_and_or, not_le] at hz
  unfold sqCut cutMode
  rcases hz with (h | h) | (h | h)
  · rw [cutoff_eq_zero hδ (Or.inl h.le)]; ring
  · rw [cutoff_eq_zero hδ (Or.inr h.le)]; ring
  · rw [cutoff_eq_zero hδ (u := z.im) (Or.inl h.le)]; ring
  · rw [cutoff_eq_zero hδ (u := z.im) (Or.inr h.le)]; ring

lemma sqCut_mem_zeroSpace {a L δ : ℝ} (hδ : 0 < δ) (p : ℕ × ℕ) :
    sqCut a L δ p ∈ zeroSpace (sqOpen a L) := by
  set K := Complex.re ⁻¹' Icc (a + δ) (a + L - δ) ∩ Complex.im ⁻¹' Icc (a + δ) (a + L - δ)
  have hKc : IsClosed K := (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)
  have hKU : K ⊆ sqOpen a L := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc
    ((isBounded_sqOpen a L).subset hKU)
  have hsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutMode a L δ k) := fun k =>
    (contDiff_cutoff a L δ).mul (contDiff_sinMode a L k)
  refine ⟨((hsm p.1).comp Complex.reCLM.contDiff).mul ((hsm p.2).comp Complex.imCLM.contDiff),
    HasCompactSupport.intro hK fun z hz => sqCut_eq_zero hδ p hz, ?_⟩
  refine (closure_minimal (fun z hz => ?_) hKc).trans hKU
  by_contra h
  exact hz (sqCut_eq_zero hδ p h)

lemma fderiv_sqCut (a L δ : ℝ) (p : ℕ × ℕ) (z : ℂ) :
    fderiv ℝ (sqCut a L δ p) z =
      (cutMode a L δ p.2 z.im * cutModeD a L δ p.1 z.re) • Complex.reCLM +
        (cutMode a L δ p.1 z.re * cutModeD a L δ p.2 z.im) • Complex.imCLM :=
  (hasFDerivAt_sep (hasDerivAt_cutMode a L δ p.1) (hasDerivAt_cutMode a L δ p.2) z).fderiv

/-- near a point of the square, `f_δ = φ_p` once `δ` is small -/
lemma sqCut_eventuallyEq {a L : ℝ} (p : ℕ × ℕ) {z : ℂ} (hz : z ∈ sqOpen a L) :
    ∀ᶠ n : ℕ in atTop, sqCut a L (1 / ((n : ℝ) + 1)) p =ᶠ[𝓝 z] sqMode a L p := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  set m := min (min (z.re - a) (a + L - z.re)) (min (z.im - a) (a + L - z.im))
  have hm : 0 < m := by
    simp only [m, lt_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hm1 : m ≤ z.re - a := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ a + L - z.re := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ z.im - a := (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : m ≤ a + L - z.im := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / m)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hδm : 2 * (1 / ((n : ℝ) + 1)) ≤ m / 2 := by
    have : (4 / m : ℝ) < n + 1 := hN.trans_le (by exact_mod_cast Nat.le_succ_of_le hn)
    rw [div_lt_iff₀ hm] at this
    rw [show 2 * (1 / ((n : ℝ) + 1)) = 2 / ((n : ℝ) + 1) by ring,
      div_le_div_iff₀ (by positivity) two_pos]
    linarith
  filter_upwards [Metric.ball_mem_nhds z (half_pos hm)] with w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hre : |w.re - z.re| < m / 2 := by
    have := Complex.abs_re_le_norm (w - z); rw [Complex.sub_re] at this; exact this.trans_lt hw
  have him : |w.im - z.im| < m / 2 := by
    have := Complex.abs_im_le_norm (w - z); rw [Complex.sub_im] at this; exact this.trans_lt hw
  rw [abs_lt] at hre him
  unfold sqCut cutMode sqMode
  rw [cutoff_eq_one hδ (by linarith) (by linarith), cutoff_eq_one hδ (by linarith) (by linarith)]
  ring

lemma ae_gradMeasure_of_mem {D : Set ℂ} (hD : MeasurableSet D) {P : ℂ × Fin 2 → Prop}
    (h : ∀ q : ℂ × Fin 2, q.1 ∈ D → P q) : ∀ᵐ q ∂gradMeasure D, P q := by
  rw [ae_iff]
  refine measure_mono_null (t := Dᶜ ×ˢ univ) (fun q hq => ⟨fun hqD => hq (h q hqD), trivial⟩) ?_
  rw [gradMeasure, Measure.prod_prod, Measure.restrict_apply hD.compl, compl_inter_self,
    measure_empty, zero_mul]

/-- **G3.** The gradient feature of a square mode lies in `gradClosure U (C_c^∞(U))`. -/
theorem gradFeat_sqMode_mem_gradClosure {a L : ℝ} (hL : 0 < L) (p : ℕ × ℕ) :
    gradFeat (sqOpen a L) (sqMode a L p) ∈ gradClosure (sqOpen a L) (zeroSpace (sqOpen a L)) := by
  obtain ⟨M, hM⟩ := exists_bound_deriv_smoothTransition
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  set f : ℕ → ℂ → ℝ := fun n => sqCut a L (δ n) p
  have hmem : ∀ n, f n ∈ zeroSpace (sqOpen a L) := fun n => sqCut_mem_zeroSpace (hδ n) p
  have : IsFiniteMeasure (volume.restrict (sqOpen a L)) :=
    isFiniteMeasure_restrict.mpr (volume_sqOpen_ne_top a L)
  have hfin : IsFiniteMeasure (gradMeasure (sqOpen a L)) := by unfold gradMeasure; infer_instance
  have hGL : ∀ n, MemLp (gradVal (f n)) 2 (gradMeasure (sqOpen a L)) := fun n =>
    memLp_gradVal ((hmem n).1.of_le (by simp)) (integrableOn_sqOpen_of_continuous
      ((((hmem n).1.of_le (by simp : (1 : WithTop ℕ∞) ≤ _)).continuous_fderiv
        one_ne_zero).norm.pow 2))
  have hA := memLp_gradVal_sqMode a L p
  have hfeat : ∀ n, gradFeat (sqOpen a L) (f n) = (hGL n).toLp _ := fun n => by
    simp [gradFeat, hGL n]
  have hann : gradFeat (sqOpen a L) (sqMode a L p) = hA.toLp _ := by simp [gradFeat, hA]
  set B : ℝ := (Real.sqrt (2 * π))⁻¹ * ((2 * M + 1) * (π * p.1 / L + π * p.2 / L)) with hB
  have hM0 : 0 ≤ M := (mul_nonneg (abs_nonneg _) (by positivity)).trans (hM 0)
  have hbound : ∀ n q, ‖gradVal (f n) q‖ ≤ B := fun n q => by
    have hc1 : 0 ≤ π * p.1 / L := by positivity
    have hc2 : 0 ≤ π * p.2 / L := by positivity
    have e1 := abs_cutModeD_le (a := a) hL (hδ n) hM p.1
    have e2 := abs_cutModeD_le (a := a) hL (hδ n) hM p.2
    have hsq : 0 ≤ (Real.sqrt (2 * π))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    simp only [f, gradVal, gradVec, fderiv_sqCut, Real.norm_eq_abs, abs_mul, abs_of_nonneg hsq]
    refine mul_le_mul_of_nonneg_left ?_ hsq
    have hm1 : 0 ≤ 2 * M + 1 := by linarith
    split_ifs
    · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, smul_eq_mul,
        mul_one, mul_zero, add_zero, abs_mul]
      calc |cutMode a L (δ n) p.2 q.1.im| * |cutModeD a L (δ n) p.1 q.1.re|
          ≤ 1 * ((2 * M + 1) * (π * p.1 / L)) :=
            mul_le_mul (abs_cutMode_le _ _ _ _ _) (e1 _) (abs_nonneg _) zero_le_one
        _ ≤ _ := by nlinarith
    · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im, smul_eq_mul,
        mul_one, mul_zero, zero_add, abs_mul]
      calc |cutMode a L (δ n) p.1 q.1.re| * |cutModeD a L (δ n) p.2 q.1.im|
          ≤ 1 * ((2 * M + 1) * (π * p.2 / L)) :=
            mul_le_mul (abs_cutMode_le _ _ _ _ _) (e2 _) (abs_nonneg _) zero_le_one
        _ ≤ _ := by nlinarith
  have hT : Tendsto (fun n => gradFeat (sqOpen a L) (f n)) atTop
      (𝓝 (gradFeat (sqOpen a L) (sqMode a L p))) := by
    simp_rw [hfeat]
    rw [hann, Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    refine tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) (fun n => (hGL n).aestronglyMeasurable) hA
      ?_ (ae_gradMeasure_of_mem (measurableSet_sqOpen a L) fun q hq => ?_)
    · refine unifIntegrable_of (by norm_num) (by norm_num) (fun n => (hGL n).aestronglyMeasurable) fun ε _ =>
        ⟨Real.toNNReal (B + 1), fun n => ?_⟩
      have h0 : {q | Real.toNNReal (B + 1) ≤ ‖gradVal (f n) q‖₊}.indicator
          (gradVal (f n)) = 0 := by
        funext q
        refine indicator_of_notMem (fun hq => ?_) _
        have hq' : ((Real.toNNReal (B + 1) : ℝ≥0) : ℝ) ≤ ‖gradVal (f n) q‖ :=
          NNReal.coe_le_coe.mpr hq
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbound 0 q)
        rw [Real.coe_toNNReal _ (by linarith)] at hq'
        linarith [hbound n q]
      rw [h0, eLpNorm_zero]
      positivity
    · refine tendsto_const_nhds.congr' ((sqCut_eventuallyEq p hq).mono fun n hn => ?_)
      simp only [f, δ, gradVal, hn.fderiv_eq]
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hT
    (Eventually.of_forall fun n => gradFeat_mem_gradClosure (hmem n))

end HeatSq
end LQGMetric
