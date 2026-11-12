/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreSl at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: a metric Slutsky lemma (tool for packet P-C)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 1 / Step 3: the localized metrics `D̂^ε` (whose locality is used, T:1231–1233) and the
metrics `D^ε` (whose limits are given by Lemma 2.5, T:1240–1256) differ by factors tending to `1`
(Lemma 2.1), so they have the same limits in law. Decision D80, packet P-C.

* `tendsto_integral_of_close` — **Slutsky** on a pseudo-metric space: if `Zₙ → Z` in law and
  `d(Ẑₙ, Zₙ) → 0` in probability, then `Ẑₙ → Z` in law (bounded Lipschitz test functions,
  mathlib `tendsto_iff_forall_lipschitz_integral_tendsto`). Standard (Billingsley, *Convergence
  of Probability Measures*, 2nd ed., Thm 3.1); mathlib has it only for normed groups
  (`tendstoInDistribution_of_tendstoInMeasure_sub`), the state spaces here are not normed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction NNReal

namespace LQGMetric.DFGPS.L217

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology E]

omit [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E] in
/-- the pointwise bound behind Slutsky's lemma -/
lemma abs_sub_le_of_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {C : ℝ}
    (hC : ∀ x y, dist (f x) (f y) ≤ C) {δ : ℝ} (hδ : 0 < δ) (a b : E) :
    |f a - f b| ≤ L * δ + C * {p : E × E | δ ≤ dist p.1 p.2}.indicator (fun _ => (1 : ℝ)) (a, b) := by
  have hC0 : 0 ≤ C := (dist_nonneg).trans (hC a a)
  by_cases h : δ ≤ dist a b
  · rw [indicator_of_mem (show (a, b) ∈ {p : E × E | δ ≤ dist p.1 p.2} from h), mul_one]
    have := hC a b
    rw [Real.dist_eq] at this
    nlinarith [NNReal.coe_nonneg L]
  · rw [indicator_of_notMem (show (a, b) ∉ {p : E × E | δ ≤ dist p.1 p.2} from h), mul_zero,
      add_zero]
    have := hf.dist_le_mul a b
    rw [Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left (not_le.1 h).le (NNReal.coe_nonneg L))

/-- **Slutsky's lemma, metric form**: if `Zₙ → Z` in law and `d(Ẑₙ, Zₙ) → 0` in probability,
then `Ẑₙ → Z` in law. -/
theorem tendsto_integral_of_close {Zn Zh : ℕ → Ω → E} {Z : Ω' → E}
    (hZn : ∀ n, Measurable (Zn n)) (hZh : ∀ n, Measurable (Zh n)) (hZ : Measurable Z)
    (hconv : ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (Zn n ω) ∂P) atTop
      (𝓝 (∫ ω, f (Z ω) ∂P')))
    (hclose : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}) atTop
      (𝓝 0)) :
    ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (Zh n ω) ∂P) atTop (𝓝 (∫ ω, f (Z ω) ∂P')) := by
  let μs : ℕ → ProbabilityMeasure E := fun n =>
    ⟨P.map (Zh n), (Measure.isProbabilityMeasure_map_iff (hZh n).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure E :=
    ⟨P'.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance⟩
  have key : Tendsto μs atTop (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc : Continuous f := hL.continuous
    have hfm : Measurable f := hfc.measurable
    show Tendsto (fun n => ∫ x, f x ∂(P.map (Zh n))) atTop (𝓝 (∫ x, f x ∂(P'.map Z)))
    simp_rw [integral_map (hZh _).aemeasurable hfm.aestronglyMeasurable,
      integral_map hZ.aemeasurable hfm.aestronglyMeasurable]
    let F : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hfc⟩ C hC
    have hF := hconv F
    change Tendsto (fun n => ∫ ω, f (Zn n ω) ∂P) atTop (𝓝 (∫ ω, f (Z ω) ∂P')) at hF
    rw [Metric.tendsto_atTop] at hF ⊢
    intro ε hε
    set δ : ℝ := ε / (3 * (L + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hC0 : 0 ≤ C := by
      obtain ⟨ω⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
      exact dist_nonneg.trans (hC (Zn 0 ω) (Zn 0 ω))
    obtain ⟨N₁, hN₁⟩ := hF (ε / 3) (by positivity)
    have hcl := hclose δ hδ0
    have hcl' : Tendsto (fun n => (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcl
      rw [ENNReal.toReal_zero] at this
      exact this
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hcl' (ε / (3 * (C + 1))) (by positivity)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have e1 := hN₁ n (le_of_max_le_left hn)
    have e2 := hN₂ n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at e2
    rw [Real.dist_eq] at e1 ⊢
    -- the swap error
    set A := {p : E × E | δ ≤ dist p.1 p.2}
    have hA : MeasurableSet A := (isClosed_le continuous_const continuous_dist).measurableSet
    have hpair : Measurable fun ω => (Zh n ω, Zn n ω) := (hZh n).prodMk (hZn n)
    have hind : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) (Zh n ω, Zn n ω)) P :=
      integrable_of_abs_le ((measurable_const.indicator hA).comp hpair) (C := 1) fun ω => by
        by_cases h : (Zh n ω, Zn n ω) ∈ A <;> simp [h]
    have hfi : ∀ (W : Ω → E), Measurable W → Integrable (fun ω => f (W ω)) P := fun W hW =>
      integrable_of_abs_le (hfm.comp hW) (C := ‖F‖) fun ω => by
        have h := F.norm_coe_le_norm (W ω)
        rw [Real.norm_eq_abs] at h
        exact h
    have hI : ∫ ω, A.indicator (fun _ => (1 : ℝ)) (Zh n ω, Zn n ω) ∂P =
        (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal := by
      rw [show (fun ω => A.indicator (fun _ => (1 : ℝ)) (Zh n ω, Zn n ω)) =
          ((fun ω => (Zh n ω, Zn n ω)) ⁻¹' A).indicator (fun _ => (1 : ℝ)) from rfl,
        integral_indicator (hpair hA), setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have herr : |∫ ω, f (Zh n ω) ∂P - ∫ ω, f (Zn n ω) ∂P| ≤
        L * δ + C * (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal := by
      have hR : ∫ ω, ((L : ℝ) * δ + C * A.indicator (fun _ => (1 : ℝ)) (Zh n ω, Zn n ω)) ∂P =
          L * δ + C * (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal := by
        rw [integral_add (integrable_const _) (hind.const_mul C), integral_const, probReal_univ,
          one_smul, integral_const_mul, hI]
      rw [← integral_sub (hfi _ (hZh n)) (hfi _ (hZn n)), ← Real.norm_eq_abs, ← hR]
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
        ((integrable_const _).add (hind.const_mul C)) (Eventually.of_forall fun ω => ?_)
      simpa [Real.norm_eq_abs] using abs_sub_le_of_lipschitz hL hC hδ0 (Zh n ω) (Zn n ω)
    have hLδ : (L : ℝ) * δ ≤ ε / 3 := by
      rw [hδ]
      have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hCp : C * (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal ≤ ε / 3 := by
      have h1 : C * (P {ω | δ ≤ dist (Zh n ω) (Zn n ω)}).toReal ≤
          (C + 1) * (ε / (3 * (C + 1))) := by
        refine mul_le_mul (by linarith) e2.le ENNReal.toReal_nonneg (by linarith)
      have h2 : (C + 1) * (ε / (3 * (C + 1))) = ε / 3 := by field_simp
      linarith
    calc |∫ ω, f (Zh n ω) ∂P - ∫ ω, f (Z ω) ∂P'|
        ≤ |∫ ω, f (Zh n ω) ∂P - ∫ ω, f (Zn n ω) ∂P| +
            |∫ ω, f (Zn n ω) ∂P - ∫ ω, f (Z ω) ∂P'| := abs_sub_le _ _ _
      _ < ε := by linarith
  intro f
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 key) f
  have hfm : Measurable fun x => f x := f.continuous.measurable
  simp only [μs, μ, ProbabilityMeasure.coe_mk] at this
  simpa [integral_map (hZh _).aemeasurable hfm.aestronglyMeasurable,
    integral_map hZ.aemeasurable hfm.aestronglyMeasurable] using this

end LQGMetric.DFGPS.L217
