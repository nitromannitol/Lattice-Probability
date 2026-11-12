/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L1_3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreFM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 1.3: joint convergence in law to a function of the fixed coordinate

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 1.3 (`lem-in-prob`,
T:381–385), cited there as Schramm–Sheffield, *Contour lines of the two-dimensional discrete
Gaussian free field*, Lemma 4.5: if `(X, Yⁿ) → (X, Y)` in law (same `X`, one probability space)
and `Y` is a.s. determined by `X`, then `Yⁿ → Y` in probability.

The paper's (commented-out) proof (T:388–398) uses tightness of the triples `(X, f(X), Yⁿ)` and
identifies subsequential limits. We use instead the fixed-marginal convergence already in the
library (`L217.tendsto_integral_mul_of_fixed_marginal`: `E[F(X)Θ(Yⁿ)] → E[F(X)Θ(Y)]` for bounded
measurable `F`, bounded continuous `Θ`) and a countable dense sequence `(b_k)` of `β`: on the
measurable piece `A_k = {f(x) ∈ B(b_k, δ)} ∖ ⋃_{j<k} {f(x) ∈ B(b_j, δ)}` one has
`1 ∧ d(y, f(x)) ≤ 1 ∧ d(y, b_k) + δ`, so `limsup E[1 ∧ d(Yⁿ, f(X))] ≤ 4δ` (own elementary argument,
no Prokhorov/Skorokhod; DEVIATIONS DFB12-1). Completeness of `β` is not used.

* `L13.tendsto_integral_min_dist` — `E[1 ∧ d(Yⁿ, f(X))] → 0`.
* `lem1_3 : Lem1_3`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

namespace L13

variable {Ω α β : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
  [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [TopologicalSpace.SeparableSpace β]

omit [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
  [MeasurableSpace β] [BorelSpace β] [TopologicalSpace.SeparableSpace β] in
/-- the pointwise covering bound on the pieces `A_k` -/
lemma min_dist_le_sum {f : α → β} {b : ℕ → β} {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ) (x : α) (y : β) :
    min 1 (dist y (f x)) ≤
      (∑ k ∈ Finset.range K,
        {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}.indicator
          (fun _ => (1 : ℝ)) x * min 1 (dist y (b k))) + δ +
      {x : α | ∀ j < K, δ ≤ dist (f x) (b j)}.indicator (fun _ => (1 : ℝ)) x := by
  have hnn : ∀ k ∈ Finset.range K, 0 ≤
      {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}.indicator
          (fun _ => (1 : ℝ)) x * min 1 (dist y (b k)) := fun k _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (le_min zero_le_one dist_nonneg)
  by_cases h : ∀ j < K, δ ≤ dist (f x) (b j)
  · rw [Set.indicator_of_mem (show x ∈ {x : α | ∀ j < K, δ ≤ dist (f x) (b j)} from h)]
    have := Finset.sum_nonneg hnn
    linarith [min_le_left (1 : ℝ) (dist y (f x))]
  · push Not at h
    classical
    let k := Nat.find h
    have hk : k < K ∧ dist (f x) (b k) < δ := Nat.find_spec h
    have hmin : ∀ j < k, δ ≤ dist (f x) (b j) := fun j hj => by
      have := Nat.find_min h hj
      push Not at this
      exact this (hj.trans hk.1)
    have hterm := Finset.single_le_sum hnn (Finset.mem_range.2 hk.1)
    rw [Set.indicator_of_mem (show x ∈ {x : α | dist (f x) (b k) < δ ∧
      ∀ j < k, δ ≤ dist (f x) (b j)} from ⟨hk.2, hmin⟩), one_mul] at hterm
    have htri : dist y (f x) ≤ dist y (b k) + δ := by
      have := dist_triangle y (b k) (f x)
      rw [dist_comm (b k)] at this
      linarith [hk.2]
    have h1 : min 1 (dist y (f x)) ≤ min 1 (dist y (b k)) + δ := by
      rcases le_total 1 (dist y (b k)) with hh | hh
      · rw [min_eq_left hh]; linarith [min_le_left (1 : ℝ) (dist y (f x))]
      · rw [min_eq_right hh]; linarith [min_le_right (1 : ℝ) (dist y (f x))]
    have h0 : 0 ≤ {x : α | ∀ j < K, δ ≤ dist (f x) (b j)}.indicator (fun _ => (1 : ℝ)) x :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    linarith

omit [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α]
  [MeasurableSpace β] [BorelSpace β] [TopologicalSpace.SeparableSpace β] in
/-- at `y = f(x)` the sum is at most `δ` (the pieces `A_k` are disjoint) -/
lemma sum_le_delta {f : α → β} {b : ℕ → β} {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ) (x : α) :
    (∑ k ∈ Finset.range K,
        {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}.indicator
          (fun _ => (1 : ℝ)) x * min 1 (dist (f x) (b k))) ≤ δ := by
  by_cases h : ∃ k ∈ Finset.range K,
      x ∈ {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}
  · obtain ⟨k, hkK, hk⟩ := h
    rw [Finset.sum_eq_single_of_mem k hkK]
    · rw [Set.indicator_of_mem hk, one_mul]
      exact (min_le_right _ _).trans (le_of_lt hk.1)
    · intro j _ hjk
      have hj : x ∉ {x : α | dist (f x) (b j) < δ ∧ ∀ i < j, δ ≤ dist (f x) (b i)} := by
        rintro ⟨hj1, hj2⟩
        rcases lt_or_gt_of_ne hjk with hlt | hlt
        · exact absurd hj1 (not_lt.2 (hk.2 j hlt))
        · exact absurd hk.1 (not_lt.2 (hj2 k hlt))
      rw [Set.indicator_of_notMem hj, zero_mul]
  · push Not at h
    rw [Finset.sum_eq_zero fun k hk => by rw [Set.indicator_of_notMem (h k hk), zero_mul]]
    exact hδ

omit [TopologicalSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α] in
lemma measurableSet_tail {f : α → β} (hf : Measurable f) (b : ℕ → β) (δ : ℝ) (K : ℕ) :
    MeasurableSet {x : α | ∀ j < K, δ ≤ dist (f x) (b j)} := by
  have : {x : α | ∀ j < K, δ ≤ dist (f x) (b j)} =
      ⋂ j, ⋂ (_ : j < K), {x : α | δ ≤ dist (f x) (b j)} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (hf.dist measurable_const)

omit [TopologicalSpace α] [BorelSpace α] [TopologicalSpace.PseudoMetrizableSpace α] in
lemma measurableSet_piece {f : α → β} (hf : Measurable f) (b : ℕ → β) (δ : ℝ) (k : ℕ) :
    MeasurableSet {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)} :=
  (measurableSet_lt (hf.dist measurable_const) measurable_const).inter
    (measurableSet_tail hf b δ k)

/-- **Key step of DFGPS Lemma 1.3**: if `(X, Yⁿ) → (X, f(X))` in law, then
`E[1 ∧ d(Yⁿ, f(X))] → 0`. -/
theorem tendsto_integral_min_dist {X : Ω → α} (hX : Measurable X) {f : α → β}
    (hf : Measurable f) {Yn : ℕ → Ω → β} (hYn : ∀ n, Measurable (Yn n))
    (hconv : ∀ φ : α × β → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X ω, f (X ω)) ∂P))) :
    Tendsto (fun n => ∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P) atTop (𝓝 0) := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty Ω := ⟨fun ω => hβ.elim (f (X ω))⟩
    exact absurd (Measure.eq_zero_of_isEmpty P) (IsProbabilityMeasure.ne_zero P)
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_dense_seq β
  have hfX : Measurable fun ω => f (X ω) := hf.comp hX
  have hnn : ∀ n ω, 0 ≤ min 1 (dist (Yn n ω) (f (X ω))) := fun _ _ =>
    le_min zero_le_one dist_nonneg
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (integral_nonneg (hnn n)), fun a ha => ?_⟩
  set δ : ℝ := a / 5 with hδdef
  have hδ : 0 < δ := by positivity
  -- the tail `P(X ∉ ⋃_{k<K} A_k) → 0`
  let E : ℕ → Set Ω := fun K => {ω | ∀ j < K, δ ≤ dist (f (X ω)) (b j)}
  have hEm : ∀ K, MeasurableSet (E K) := fun K => hX (measurableSet_tail hf b δ K)
  have hEanti : Antitone E := fun K L hKL ω hω j hj => hω j (lt_of_lt_of_le hj hKL)
  have hEempty : (⋂ K, E K) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 hb (f (X ω)) δ hδ
    exact ⟨j + 1, fun h => absurd (h j (Nat.lt_succ_self j)) (not_le.2 hj)⟩
  have htail : Tendsto (fun K => P (E K)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun K => (hEm K).nullMeasurableSet) hEanti
      ⟨0, measure_ne_top P _⟩
    rwa [hEempty, measure_empty] at this
  obtain ⟨K, hK⟩ := (htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))).exists
  have hKr : P.real (E K) < δ := by
    rw [measureReal_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top P _) ENNReal.ofReal_ne_top).2 hK |>.trans_le
      (ENNReal.toReal_ofReal hδ.le).le
  -- the pieces
  let A : ℕ → Set α := fun k => {x : α | dist (f x) (b k) < δ ∧ ∀ j < k, δ ≤ dist (f x) (b j)}
  let F : ℕ → α → ℝ := fun k => (A k).indicator fun _ => (1 : ℝ)
  let Θ : ℕ → β → ℝ := fun k y => min 1 (dist y (b k))
  have hFm : ∀ k, Measurable (F k) := fun k =>
    (measurable_const.indicator (measurableSet_piece hf b δ k))
  have hFb : ∀ k x, |F k x| ≤ 1 := fun k x => by
    simp only [F, Set.indicator]; split_ifs <;> simp
  have hΘc : ∀ k, Continuous (Θ k) := fun k =>
    continuous_const.min (continuous_id.dist continuous_const)
  have hΘb : ∀ k y, |Θ k y| ≤ 1 := fun k y => by
    rw [abs_of_nonneg (le_min zero_le_one dist_nonneg)]; exact min_le_left _ _
  have hint : ∀ k (Z : Ω → β), Measurable Z → Integrable (fun ω => F k (X ω) * Θ k (Z ω)) P :=
    fun k Z hZ => L217.integrable_of_abs_le (((hFm k).comp hX).mul
      ((hΘc k).measurable.comp hZ)) (C := 1) fun ω => by
        rw [abs_mul]; nlinarith [hFb k (X ω), hΘb k (Z ω), abs_nonneg (F k (X ω)),
          abs_nonneg (Θ k (Z ω))]
  have hlim : Tendsto (fun n => ∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) atTop
      (𝓝 (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (f (X ω)) ∂P)) :=
    tendsto_finsetSum _ fun k _ =>
      L217.tendsto_integral_mul_of_fixed_marginal hX hYn hfX hconv (hFm k) (hFb k) (hΘc k)
        (hΘb k)
  have hlimle : (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (f (X ω)) ∂P) ≤ δ := by
    rw [← integral_finsetSum _ fun k _ => hint k _ hfX]
    calc _ ≤ ∫ _ : Ω, δ ∂P := integral_mono_of_nonneg
            (Eventually.of_forall fun ω => Finset.sum_nonneg fun k _ =>
              mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
                (le_min zero_le_one dist_nonneg))
            (integrable_const δ) (Eventually.of_forall fun ω => sum_le_delta hδ.le K (X ω))
      _ = δ := by simp
  have hev : ∀ᶠ n in atTop,
      (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) < 2 * δ :=
    hlim.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev] with n hn
  have hbound : ∀ ω, min 1 (dist (Yn n ω) (f (X ω))) ≤
      (∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ +
        (E K).indicator (fun _ => (1 : ℝ)) ω := fun ω => by
    have := min_dist_le_sum (f := f) (b := b) hδ.le K (X ω) (Yn n ω)
    simpa [E, Set.indicator, F, A, Θ] using this
  have hIE : Integrable ((E K).indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator (hEm K)
  have hIS : Integrable (fun ω => ∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) P :=
    integrable_finsetSum _ fun k _ => hint k _ (hYn n)
  have hISd : Integrable (fun ω => (∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ) P :=
    hIS.add (integrable_const δ)
  calc ∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P
      ≤ ∫ ω, ((∑ k ∈ Finset.range K, F k (X ω) * Θ k (Yn n ω)) + δ +
          (E K).indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall (hnn n))
          (hISd.add hIE) (Eventually.of_forall hbound)
    _ = (∑ k ∈ Finset.range K, ∫ ω, F k (X ω) * Θ k (Yn n ω) ∂P) + δ + P.real (E K) := by
        rw [integral_add hISd hIE, integral_add hIS (integrable_const δ),
          integral_finsetSum _ fun k _ => hint k _ (hYn n)]
        simp [integral_indicator (hEm K), measureReal_def]
    _ < a := by linarith

end L13

/-- **DFGPS Lemma 1.3** (`lem-in-prob`, T:381–385; Schramm–Sheffield, Lemma 4.5). -/
theorem lem1_3 : Lem1_3 := by
  intro Ω α β _ _ _ _ _ _ _ _ _ P _ X Y Yn hX hY hYn hconv hdet
  obtain ⟨f, hf, hYf⟩ := hdet
  have hconv' : ∀ φ : α × β → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (X ω, Yn n ω) ∂P) atTop (𝓝 (∫ ω, φ (X ω, f (X ω)) ∂P)) := by
    intro φ hφ hb
    have he : (∫ ω, φ (X ω, Y ω) ∂P) = ∫ ω, φ (X ω, f (X ω)) ∂P :=
      integral_congr_ae (hYf.mono fun ω h => by simp only [h, Function.comp_apply])
    rw [← he]; exact hconv φ hφ hb
  have key := L13.tendsto_integral_min_dist hX hf hYn hconv'
  refine TendstoInMeasure.congr_right (g := fun ω => f (X ω)) (hYf.mono fun ω h => h.symm) ?_
  refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
  set e : ℝ := min 1 ε.toReal with he
  have hepos : 0 < e := lt_min one_pos (ENNReal.toReal_pos hε.ne' hεt)
  have hint : ∀ n, Integrable (fun ω => min 1 (dist (Yn n ω) (f (X ω)))) P := fun n =>
    L217.integrable_of_abs_le (measurable_const.min ((hYn n).dist (hf.comp hX))) (C := 1) fun ω => by
      rw [abs_of_nonneg (le_min zero_le_one dist_nonneg)]; exact min_le_left _ _
  have hle : ∀ n, P {ω | ε ≤ edist (Yn n ω) (f (X ω))} ≤
      ENNReal.ofReal ((∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P) / e) := fun n => by
    have hsub : {ω | ε ≤ edist (Yn n ω) (f (X ω))} ⊆
        {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))} := fun ω hω => by
      have h1 : ε.toReal ≤ dist (Yn n ω) (f (X ω)) := by
        have hω' : ε ≤ edist (Yn n ω) (f (X ω)) := hω
        rw [edist_dist] at hω'; exact ENNReal.toReal_le_of_le_ofReal dist_nonneg hω'
      exact min_le_min_left _ h1
    have hM := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Eventually.of_forall fun ω => le_min zero_le_one dist_nonneg) (hint n) e
    calc _ ≤ P {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | e ≤ min 1 (dist (Yn n ω) (f (X ω)))}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hepos]; linarith)
  have hto : Tendsto (fun n => ENNReal.ofReal ((∫ ω, min 1 (dist (Yn n ω) (f (X ω))) ∂P) / e))
      atTop (𝓝 0) := by
    have h0 := key.div_const e
    rw [zero_div] at h0
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto (fun _ => zero_le) hle

end LQGMetric.DFGPS
