/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_13Conv at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.13, packet 3 (abstract part): adjoining a measurable function of the field

Setting of DFGPS Lemma 2.13 (`lem-lfpp-coord`, arXiv:1905.00380, `lqg-metric-estimates-final.tex`
T:1104–1119): `(X, Y_n) → (X, Y)` jointly in law, with the *same* first coordinate `X` for every
`n` (the field `h`). The paper pushes this through `(h, d) ↦ e^{−ξ h_r(0)} d(r·, r·)`; the circle
average `h_r(0)` is not a continuous function of `h`, but it is an a.s. limit of continuous
functions `g_m(h)` of `h` (pairings with mollified circle measures). Since `X` does not depend on
`n`, the approximation error is uniform in `n`, and `((A, s_n), Y_n) → ((A, s), Y)` in law for any
a.s. limit `A` of `g_m(X)` and any deterministic `s_n → s` (`tendstoInDistribution_adjoin`).
Proof: test against bounded Lipschitz functions (mathlib
`tendsto_iff_forall_lipschitz_integral_tendsto`) and a three-term estimate. Own elementary
argument (DEC-78 §4 packet 3 prescribes it; the paper does not spell this step out).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace LQGMetric.DFGPS.L213

variable {Ω α β : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace α] [MeasurableSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
  [SecondCountableTopology β]

lemma min_add_le (C a b : ℝ) (hb : 0 ≤ b) : min C (a + b) ≤ min C a + b := by
  rcases le_total C a with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith [min_eq_left (le_trans h (le_add_of_nonneg_right hb))])
  · rw [min_eq_right h]; exact min_le_right _ _

/-- **Adjoining an a.s. limit of continuous functions of the fixed coordinate.** -/
theorem tendstoInDistribution_adjoin (X : Ω → α) (hX : Measurable X) (Y : ℕ → Ω → β)
    (Yl : Ω → β) (hY : ∀ n, AEMeasurable (Y n) P) (hYl : AEMeasurable Yl P)
    (H : ∀ φ : α × β → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Y n ω) ∂P) atTop (𝓝 (∫ ω, φ (X ω, Yl ω) ∂P)))
    (g : ℕ → α → ℝ) (hgc : ∀ m, Continuous (g m)) (hgm : ∀ m, Measurable (g m))
    (A : Ω → ℝ) (hA : AEMeasurable A P)
    (hgA : ∀ᵐ ω ∂P, Tendsto (fun m => g m (X ω)) atTop (𝓝 (A ω)))
    (s : ℕ → ℝ) (sl : ℝ) (hs : Tendsto s atTop (𝓝 sl)) :
    TendstoInDistribution (fun n ω => ((A ω, s n), Y n ω)) atTop (fun ω => ((A ω, sl), Yl ω))
      (fun _ => P) P where
  forall_aemeasurable n := (hA.prodMk aemeasurable_const).prodMk (hY n)
  aemeasurable_limit := (hA.prodMk aemeasurable_const).prodMk hYl
  tendsto := by
    let _ : PseudoMetricSpace β := TopologicalSpace.pseudoMetrizableSpacePseudoMetric β
    refine (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := (ℝ × ℝ) × β)).2 ?_
    rintro F ⟨C0, hC0⟩ ⟨L, hL⟩
    obtain ⟨ω0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
    set C := max C0 0
    have hC : ∀ u v, |F u - F v| ≤ C := fun u v => (hC0 u v).trans (le_max_left _ _)
    have hC0' : 0 ≤ C := le_max_right _ _
    have hFc : Continuous F := hL.continuous
    set u0 : (ℝ × ℝ) × β := ((0, 0), Yl ω0)
    have hFb : ∀ u, |F u| ≤ |F u0| + C := fun u => by
      have := hC u u0; have := abs_sub_abs_le_abs_sub (F u) (F u0); linarith
    have hint : ∀ Z : Ω → (ℝ × ℝ) × β, AEMeasurable Z P → Integrable (fun ω => F (Z ω)) P :=
      fun Z hZ => Integrable.of_bound (hFc.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
        (|F u0| + C) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hFb _)
    have hlip : ∀ (a a' t t' : ℝ) (y : β), |F ((a, t), y) - F ((a', t'), y)| ≤
        min C (L * (|a - a'| + |t - t'|)) := by
      intro a a' t t' y
      refine le_min (hC _ _) ?_
      have h1 := hL.dist_le_mul ((a, t), y) ((a', t'), y)
      rw [Real.dist_eq] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
      simp only [Prod.dist_eq, dist_self, Real.dist_eq]
      refine max_le (max_le ?_ ?_) (by positivity)
      · linarith [abs_nonneg (t - t')]
      · linarith [abs_nonneg (a - a')]
    -- the uniform approximation error
    set e : ℕ → ℝ := fun m => ∫ ω, min C (L * |A ω - g m (X ω)|) ∂P
    have hGm : ∀ m, AEMeasurable (fun ω => g m (X ω)) P :=
      fun m => ((hgm m).comp hX).aemeasurable
    have he : Tendsto e atTop (𝓝 0) := by
      have : (0 : ℝ) = ∫ ω, (0 : ℝ) ∂P := by simp
      rw [this]
      refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun m => ?_)
        (integrable_const C) (fun m => Eventually.of_forall fun ω => ?_) ?_
      · exact (((continuous_const.min (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
          (hA.sub (hGm m)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_min hC0' (by positivity))]
        exact min_le_left _ _
      · filter_upwards [hgA] with ω hω
        have h1 : Tendsto (fun m => L * |A ω - g m (X ω)|) atTop (𝓝 (L * |A ω - A ω|)) :=
          ((tendsto_const_nhds.sub hω).abs).const_mul _
        rw [sub_self, abs_zero, mul_zero] at h1
        have h2 := (tendsto_const_nhds (x := C)).min h1
        rwa [min_eq_right hC0'] at h2
    have hi : ∀ (Z : Ω → (ℝ × ℝ) × β), AEMeasurable Z P →
        ∫ x, F x ∂(P.map Z) = ∫ ω, F (Z ω) ∂P := fun Z hZ =>
      integral_map hZ hFc.aestronglyMeasurable
    simp only [ProbabilityMeasure.coe_mk]
    rw [hi _ ((hA.prodMk aemeasurable_const).prodMk hYl)]
    simp only [fun n => hi _ ((hA.prodMk aemeasurable_const).prodMk (hY n))]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := ((he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).exists)
    set φ : α × β → ℝ := fun x => F ((g m x.1, sl), x.2)
    have hφc : Continuous φ := hFc.comp (((hgc m).comp continuous_fst).prodMk continuous_const
      |>.prodMk continuous_snd)
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 (H φ hφc ⟨_, fun x => hFb _⟩) (ε / 4)
      (by positivity)
    have hsL : Tendsto (fun n => (L : ℝ) * |s n - sl|) atTop (𝓝 0) := by
      have := ((hs.sub_const sl).abs).const_mul (L : ℝ)
      simpa using this
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 hsL (ε / 4) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have h1 := hN1 n (le_of_max_le_left hn)
    have h2 := hN2 n (le_of_max_le_right hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
    rw [Real.dist_eq] at h1 ⊢
    have hZn : AEMeasurable (fun ω => ((A ω, s n), Y n ω)) P :=
      (hA.prodMk aemeasurable_const).prodMk (hY n)
    have hZl : AEMeasurable (fun ω => ((A ω, sl), Yl ω)) P :=
      (hA.prodMk aemeasurable_const).prodMk hYl
    have hWn : AEMeasurable (fun ω => ((g m (X ω), sl), Y n ω)) P :=
      ((hGm m).prodMk aemeasurable_const).prodMk (hY n)
    have hWl : AEMeasurable (fun ω => ((g m (X ω), sl), Yl ω)) P :=
      ((hGm m).prodMk aemeasurable_const).prodMk hYl
    have hEi : Integrable (fun ω => min C (L * |A ω - g m (X ω)|)) P :=
      Integrable.of_bound ((((continuous_const.min (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
          (hA.sub (hGm m)))).aestronglyMeasurable) C (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_min hC0' (by positivity))]
            exact min_le_left _ _)
    -- first term
    have t1 : |∫ ω, F ((A ω, s n), Y n ω) ∂P - ∫ ω, F ((g m (X ω), sl), Y n ω) ∂P| ≤
        e m + L * |s n - sl| := by
      rw [← integral_sub (hint _ hZn) (hint _ hWn)]
      refine (abs_integral_le_integral_abs).trans ?_
      have : ∫ ω, (min C (L * |A ω - g m (X ω)|) + L * |s n - sl|) ∂P =
          e m + L * |s n - sl| := by
        rw [integral_add hEi (integrable_const _), integral_const]; simp [e]
      rw [← this]
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (hEi.add (integrable_const _)) (Eventually.of_forall fun ω => ?_)
      refine (hlip _ _ _ _ _).trans ?_
      rw [mul_add]
      exact min_add_le _ _ _ (by positivity)
    have t3 : |∫ ω, F ((g m (X ω), sl), Yl ω) ∂P - ∫ ω, F ((A ω, sl), Yl ω) ∂P| ≤ e m := by
      rw [← integral_sub (hint _ hWl) (hint _ hZl)]
      refine (abs_integral_le_integral_abs).trans ?_
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hEi
        (Eventually.of_forall fun ω => ?_)
      refine (hlip _ _ _ _ _).trans ?_
      simp only [sub_self, abs_zero, add_zero, abs_sub_comm (g m (X ω))]
      exact le_rfl
    have hem : e m < ε / 4 := hm
    calc |∫ ω, F ((A ω, s n), Y n ω) ∂P - ∫ ω, F ((A ω, sl), Yl ω) ∂P|
        ≤ |∫ ω, F ((A ω, s n), Y n ω) ∂P - ∫ ω, F ((g m (X ω), sl), Y n ω) ∂P| +
          |∫ ω, F ((g m (X ω), sl), Y n ω) ∂P - ∫ ω, F ((g m (X ω), sl), Yl ω) ∂P| +
          |∫ ω, F ((g m (X ω), sl), Yl ω) ∂P - ∫ ω, F ((A ω, sl), Yl ω) ∂P| := by
          have := abs_sub_le (∫ ω, F ((A ω, s n), Y n ω) ∂P)
            (∫ ω, F ((g m (X ω), sl), Y n ω) ∂P) (∫ ω, F ((A ω, sl), Yl ω) ∂P)
          have := abs_sub_le (∫ ω, F ((g m (X ω), sl), Y n ω) ∂P)
            (∫ ω, F ((g m (X ω), sl), Yl ω) ∂P) (∫ ω, F ((A ω, sl), Yl ω) ∂P)
          linarith
      _ < ε := by linarith

end LQGMetric.DFGPS.L213
