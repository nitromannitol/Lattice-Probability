/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17CoreRc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreSl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: multiplicative closeness gives closeness in probability

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 2.1
(T:648–650): a.s., for every `c > 1` and all small `ε`, `D̂^ε_h ≤ c D^ε_h` and `D^ε_h ≤ c D̂^ε_h`
on a bounded set. Combined with the tightness of `𝔞_ε⁻¹ D^ε_h(·,·;W̄)` (Lemma 2.9), the
difference of the rescaled metrics tends to `0` in probability (the input of
`tendsto_integral_of_close`). Decision D80, packet P-C (swap of Step 1). Own standard argument.

* `tendsto_measure_of_ae_eventually_notMem` — `P(Eₙ) → 0` when a.s. `ω ∉ Eₙ` eventually.
* `tendsto_measure_norm_sub_of_ratio` — if `Zₙ → Z` in law in a normed group and a.s., for every
  `c > 1`, eventually `‖Ẑₙ − Zₙ‖ ≤ (c − 1)‖Zₙ‖`, then `‖Ẑₙ − Zₙ‖ → 0` in probability.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction NNReal

namespace LQGMetric.DFGPS.L217

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- a.s. eventual non-membership gives `P(Eₙ) → 0` -/
theorem tendsto_measure_of_ae_eventually_notMem {E : ℕ → Set Ω} (hE : ∀ n, MeasurableSet (E n))
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E n) : Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
  set F : ℕ → Set Ω := fun n => ⋃ m ≥ n, E m
  have hF : ∀ n, NullMeasurableSet (F n) P := fun n =>
    (MeasurableSet.biUnion (to_countable _) fun m _ => hE m).nullMeasurableSet
  have hanti : Antitone F := fun n n' hnn' => biUnion_subset_biUnion_left fun m hm =>
    le_trans hnn' hm
  have h0 : P (⋂ n, F n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    simp only [F, mem_iInter, mem_iUnion, not_forall, not_exists]
    exact ⟨N, fun m hm => hN m hm⟩
  have hlim := tendsto_measure_iInter_atTop hF hanti ⟨0, measure_ne_top _ _⟩
  rw [h0] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun n => measure_mono (subset_biUnion_of_mem (u := E) (le_refl n))

variable {T : Type*} [NormedAddCommGroup T] [MeasurableSpace T] [BorelSpace T]
  [SecondCountableTopology T]

/-- **multiplicative closeness ⇒ closeness in probability** -/
theorem tendsto_measure_norm_sub_of_ratio {Zn Zh : ℕ → Ω → T} {Z : Ω' → T}
    (hZn : ∀ n, Measurable (Zn n)) (hZh : ∀ n, Measurable (Zh n)) (hZ : Measurable Z)
    (hconv : ∀ f : T →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (Zn n ω) ∂P) atTop
      (𝓝 (∫ ω, f (Z ω) ∂P')))
    (hratio : ∀ c : ℝ, 1 < c → ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ‖Zh n ω - Zn n ω‖ ≤ (c - 1) * ‖Zn n ω‖)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ ≤ ‖Zh n ω - Zn n ω‖}) atTop (𝓝 0) := by
  -- the laws of `Zₙ` converge
  let μs : ℕ → ProbabilityMeasure T := fun n =>
    ⟨P.map (Zn n), (Measure.isProbabilityMeasure_map_iff (hZn n).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure T :=
    ⟨P'.map Z, (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance⟩
  have hlaw : Tendsto μs atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hfm : Measurable fun x => f x := f.continuous.measurable
    show Tendsto (fun n => ∫ x, f x ∂(P.map (Zn n))) atTop (𝓝 (∫ x, f x ∂(P'.map Z)))
    simp_rw [integral_map (hZn _).aemeasurable hfm.aestronglyMeasurable,
      integral_map hZ.aemeasurable hfm.aestronglyMeasurable]
    exact hconv f
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- a level `M` with `P'(‖Z‖ ≥ M) < ε / 2`
  have hball : Tendsto (fun M : ℕ => P' {ω | (M : ℝ) ≤ ‖Z ω‖}) atTop (𝓝 0) := by
    have hm : ∀ M : ℕ, NullMeasurableSet {ω | (M : ℝ) ≤ ‖Z ω‖} P' := fun M =>
      (measurableSet_le measurable_const hZ.norm).nullMeasurableSet
    have hanti : Antitone fun M : ℕ => {ω | (M : ℝ) ≤ ‖Z ω‖} :=
      fun M M' hMM' ω (hω : (M' : ℝ) ≤ ‖Z ω‖) =>
        show (M : ℝ) ≤ ‖Z ω‖ from le_trans (by exact_mod_cast hMM') hω
    have := tendsto_measure_iInter_atTop hm hanti ⟨0, measure_ne_top _ _⟩
    have he : (⋂ M : ℕ, {ω | (M : ℝ) ≤ ‖Z ω‖}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨M, hM⟩ := exists_nat_gt ‖Z ω‖
      exact ⟨M, hM⟩
    rwa [he, measure_empty] at this
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 ((tendsto_order.1 hball).2 _ hε2)
  set M : ℝ := (M₀ : ℝ) + 1 with hM
  have hMpos : 0 < M := by positivity
  have hZM : P' {ω | M ≤ ‖Z ω‖} < ε / 2 :=
    lt_of_le_of_lt (measure_mono fun ω (hω : M ≤ ‖Z ω‖) =>
      show ((M₀ : ℕ) : ℝ) ≤ ‖Z ω‖ by linarith) (hM₀ M₀ le_rfl)
  -- `limsup P(‖Zₙ‖ ≥ M) ≤ P'(‖Z‖ ≥ M)`
  have hclosed : IsClosed {x : T | M ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlaw hclosed
  have hls' : limsup (fun n => P {ω | M ≤ ‖Zn n ω‖}) atTop < ε / 2 := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hls ?_)
    · congr 1; funext n
      show P {ω | M ≤ ‖Zn n ω‖} = (P.map (Zn n)) {x | M ≤ ‖x‖}
      rw [Measure.map_apply (hZn n) hclosed.measurableSet]; rfl
    · show (P'.map Z) {x | M ≤ ‖x‖} < ε / 2
      rw [Measure.map_apply hZ hclosed.measurableSet]; exact hZM
  have hev1 : ∀ᶠ n in atTop, P {ω | M ≤ ‖Zn n ω‖} < ε / 2 :=
    eventually_lt_of_limsup_lt hls'
  -- the bad events
  set c : ℝ := 1 + δ / (2 * M) with hc
  have hc1 : 1 < c := by have : 0 < δ / (2 * M) := by positivity
                         linarith
  set En : ℕ → Set Ω := fun n => {ω | δ ≤ ‖Zh n ω - Zn n ω‖} ∩ {ω | ‖Zn n ω‖ < M}
  have hEn : ∀ n, MeasurableSet (En n) := fun n =>
    (measurableSet_le measurable_const ((hZh n).sub (hZn n)).norm).inter
      (measurableSet_lt (hZn n).norm measurable_const)
  have hEev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ En n := by
    filter_upwards [hratio c hc1] with ω hω
    filter_upwards [hω] with n hn
    rintro ⟨h1, h2⟩
    have h1' : δ ≤ ‖Zh n ω - Zn n ω‖ := h1
    have h2' : ‖Zn n ω‖ < M := h2
    have : (c - 1) * ‖Zn n ω‖ < δ := by
      rw [hc, add_sub_cancel_left]
      calc δ / (2 * M) * ‖Zn n ω‖ ≤ δ / (2 * M) * M := by gcongr
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    linarith
  have hev2 : ∀ᶠ n in atTop, P (En n) < ε / 2 :=
    (tendsto_order.1 (tendsto_measure_of_ae_eventually_notMem hEn hEev)).2 _ hε2
  filter_upwards [hev1, hev2] with n h1 h2
  calc P {ω | δ ≤ ‖Zh n ω - Zn n ω‖} ≤ P ({ω | M ≤ ‖Zn n ω‖} ∪ En n) := by
        refine measure_mono fun ω hω => ?_
        by_cases hM' : M ≤ ‖Zn n ω‖
        · exact Or.inl hM'
        · exact Or.inr ⟨hω, not_le.1 hM'⟩
    _ ≤ P {ω | M ≤ ‖Zn n ω‖} + P (En n) := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1.le h2.le
    _ = ε := ENNReal.add_halves ε

end LQGMetric.DFGPS.L217
