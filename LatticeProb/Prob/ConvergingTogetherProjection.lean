import Mathlib

/-!
# Converging together with a projected coordinate

Let `D n` be random elements of a space `S` (the data), `Q n` random elements of a space `𝒞`, such
that `(D n, Q n)` converges in law to a probability measure `ν` on `S × 𝒞` (integrals of bounded
continuous functions converge). Let `π : S → M` be continuous, with `M` a pseudo-metric space, and let
`Y n` be random elements of `M` with `dist (Y n) (π (D n)) → 0` in probability. If moreover the
deterministic times `s n` converge to `s₀`, then `(D n, Y n, Q n, s n)` converges in law to the image
of `ν` under `(d, q) ↦ (d, π d, q, s₀)`.

This is the continuous mapping theorem for `(d, q) ↦ (d, π d, q, s₀)` followed by converging together
in the coordinates of `M` and of `ℝ≥0` (Billingsley, *Convergence of probability measures*,
Theorems 2.7 and 3.1), with bounded Lipschitz test functions on the product pseudo-metric space
(`tendsto_iff_forall_lipschitz_integral_tendsto`).

* `LatticeProb.abs_integral_comp_sub_le_of_dist_le_add`: for a bounded Lipschitz `F`, if
  `dist (U ω) (V ω) ≤ e ω + a`, then `|𝔼 F (U) - 𝔼 F (V)| ≤ L η + L a + C ℙ(η ≤ e)`.
* `LatticeProb.tendsto_integral_projection_of_tendstoInMeasure_dist_of_pseudoMetricSpace`: the
  statement for pseudo-metric spaces `S`, `𝒞` and measurable random elements.
* `LatticeProb.tendsto_integral_projection_of_tendstoInMeasure_dist_of_measurable`: the statement
  for pseudo-metrizable second countable Borel spaces `S`, `𝒞`, almost everywhere measurable random
  elements and a measurable `π`.
* `LatticeProb.tendsto_integral_projection_of_tendstoInMeasure_dist`: the same with `M` Borel.
* `LatticeProb.tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist`: the
  case of finite measures on `ℂ` with the Lévy-Prokhorov distance, `M = LevyProkhorov (FiniteMeasure ℂ)`
  (the pseudo-metric space of finite measures that Mathlib provides).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

/-- A bounded Lipschitz function of two random elements `U, V` of a pseudo-metric space with
`dist (U ω) (V ω) ≤ e ω + a` differs in mean by at most `L η + L a`, plus the bound `C` on the
oscillation of `F` times the outer probability of `η ≤ e`. -/
theorem abs_integral_comp_sub_le_of_dist_le_add {Ω W : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [PseudoMetricSpace W] [MeasurableSpace W]
    [OpensMeasurableSpace W] {U V : Ω → W} (hU : Measurable U) (hV : Measurable V) {F : W → ℝ}
    {C : ℝ} {L : ℝ≥0} (hC : ∀ x y, dist (F x) (F y) ≤ C) (hF : LipschitzWith L F)
    {e : Ω → ℝ} {a η : ℝ} (ha : 0 ≤ a) (hη : 0 ≤ η) (he : ∀ ω, dist (U ω) (V ω) ≤ e ω + a) :
    |∫ ω, F (U ω) ∂P - ∫ ω, F (V ω) ∂P| ≤ L * η + L * a + C * P.real {ω | η ≤ e ω} := by
  have hFm : Measurable F := hF.continuous.measurable
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hC0 : 0 ≤ C := dist_nonneg.trans (hC (U ω₀) (U ω₀))
  have hbd : ∀ x, ‖F x‖ ≤ ‖F (U ω₀)‖ + C := fun x => by
    have h1 := abs_sub_abs_le_abs_sub (F x) (F (U ω₀))
    have h2 := hC x (U ω₀)
    rw [Real.dist_eq] at h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have hIU : Integrable (fun ω => F (U ω)) P :=
    Integrable.of_bound (hFm.comp hU).aestronglyMeasurable (‖F (U ω₀)‖ + C)
      (ae_of_all _ fun ω => hbd _)
  have hIV : Integrable (fun ω => F (V ω)) P :=
    Integrable.of_bound (hFm.comp hV).aestronglyMeasurable (‖F (U ω₀)‖ + C)
      (ae_of_all _ fun ω => hbd _)
  obtain ⟨T, hsub, hTm, hPT⟩ : ∃ T : Set Ω, {ω | η ≤ e ω} ⊆ T ∧ MeasurableSet T ∧
      P.real T = P.real {ω | η ≤ e ω} :=
    ⟨toMeasurable P {ω | η ≤ e ω}, subset_toMeasurable _ _, measurableSet_toMeasurable _ _, by
      rw [measureReal_def, measureReal_def, measure_toMeasurable]⟩
  have hIrhs : Integrable (fun ω => (L : ℝ) * η + L * a + T.indicator (fun _ => C) ω) P :=
    (integrable_const _).add ((integrable_const C).indicator hTm)
  rw [← integral_sub hIU hIV, ← Real.norm_eq_abs, ← hPT]
  calc ‖∫ ω, (F (U ω) - F (V ω)) ∂P‖ ≤ ∫ ω, ‖F (U ω) - F (V ω)‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((L : ℝ) * η + L * a + T.indicator (fun _ => C) ω) ∂P := by
        refine integral_mono (hIU.sub hIV).norm hIrhs fun ω => ?_
        have hLη : (0 : ℝ) ≤ L * η := mul_nonneg L.2 hη
        have hLa : (0 : ℝ) ≤ L * a := mul_nonneg L.2 ha
        have hind : 0 ≤ T.indicator (fun _ => C) ω := Set.indicator_nonneg (fun _ _ => hC0) ω
        by_cases h : η ≤ e ω
        · rw [Set.indicator_of_mem (hsub h)]
          have h3 := hC (U ω) (V ω)
          rw [dist_eq_norm] at h3
          linarith
        · have h1 := hF.dist_le_mul (U ω) (V ω)
          rw [dist_eq_norm] at h1
          have h2 : (L : ℝ) * dist (U ω) (V ω) ≤ L * (η + a) :=
            mul_le_mul_of_nonneg_left ((he ω).trans (by linarith [not_le.1 h])) L.2
          rw [mul_add] at h2
          linarith
    _ = (L : ℝ) * η + L * a + C * P.real T := by
        rw [integral_add (integrable_const _) ((integrable_const C).indicator hTm),
          integral_const, integral_indicator_const _ hTm]
        simp [mul_comm]

/-- **Converging together with a projected coordinate**, pseudo-metric form. Let `S`, `𝒞` be second
countable pseudo-metric spaces, `M` a pseudo-metric space whose open sets are measurable,
`π : S → M` continuous and measurable, and `D n`, `Q n`, `Y n` measurable random elements of `S`,
`𝒞`, `M`. If `(D n, Q n)` converges in law to `ν` on `S × 𝒞`, `dist (Y n) (π (D n)) → 0` in
probability and `s n → s₀`, then `(D n, Y n, Q n, s n)` converges in law to the image of `ν` under
`(d, q) ↦ (d, π d, q, s₀)`. -/
theorem tendsto_integral_projection_of_tendstoInMeasure_dist_of_pseudoMetricSpace
    {Ω S M 𝒞 : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [PseudoMetricSpace S] [SecondCountableTopology S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    [PseudoMetricSpace 𝒞] [SecondCountableTopology 𝒞] [MeasurableSpace 𝒞] [OpensMeasurableSpace 𝒞]
    {D : ℕ → Ω → S} (hD : ∀ n, Measurable (D n)) {Y : ℕ → Ω → M} (hY : ∀ n, Measurable (Y n))
    {Q : ℕ → Ω → 𝒞} (hQ : ∀ n, Measurable (Q n)) {s : ℕ → ℝ≥0} {s₀ : ℝ≥0} {π : S → M}
    (hπ : Continuous π) (hπm : Measurable π) {ν : Measure (S × 𝒞)}
    (hlaw : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω, Q n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hYπ : TendstoInMeasure P (fun n ω => dist (Y n ω) (π (D n ω))) atTop 0)
    (hs : Tendsto s atTop (𝓝 s₀)) (G : (S × M × 𝒞 × ℝ≥0) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, G (D n ω, Y n ω, Q n ω, s n) ∂P) atTop
      (𝓝 (∫ p, G (p.1, π p.1, p.2, s₀) ∂ν)) := by
  have h1 : ν.real Set.univ = 1 := by
    have h := hlaw 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hν : IsProbabilityMeasure ν :=
    ⟨by rw [measureReal_def] at h1; exact (ENNReal.toReal_eq_one_iff _).1 h1⟩
  have hΦc : Continuous fun p : S × 𝒞 => ((p.1, π p.1, p.2, s₀) : S × M × 𝒞 × ℝ≥0) :=
    continuous_fst.prodMk ((hπ.comp continuous_fst).prodMk
      (continuous_snd.prodMk continuous_const))
  have hΦm : Measurable fun p : S × 𝒞 => ((p.1, π p.1, p.2, s₀) : S × M × 𝒞 × ℝ≥0) :=
    measurable_fst.prodMk ((hπm.comp measurable_fst).prodMk
      (measurable_snd.prodMk measurable_const))
  have hB : ∀ n, Measurable fun ω => ((D n ω, Y n ω, Q n ω, s n) : S × M × 𝒞 × ℝ≥0) :=
    fun n => (hD n).prodMk ((hY n).prodMk ((hQ n).prodMk measurable_const))
  have hA : ∀ n, Measurable fun ω => ((D n ω, π (D n ω), Q n ω, s₀) : S × M × 𝒞 × ℝ≥0) :=
    fun n => hΦm.comp ((hD n).prodMk (hQ n))
  have hΦν : IsProbabilityMeasure
      (ν.map fun p : S × 𝒞 => ((p.1, π p.1, p.2, s₀) : S × M × 𝒞 × ℝ≥0)) :=
    (Measure.isProbabilityMeasure_map_iff hΦm.aemeasurable).2 hν
  let μs : ℕ → ProbabilityMeasure (S × M × 𝒞 × ℝ≥0) := fun n =>
    ⟨P.map fun ω => (D n ω, Y n ω, Q n ω, s n),
      (Measure.isProbabilityMeasure_map_iff (hB n).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure (S × M × 𝒞 × ℝ≥0) :=
    ⟨ν.map fun p : S × 𝒞 => ((p.1, π p.1, p.2, s₀) : S × M × 𝒞 × ℝ≥0), hΦν⟩
  have hη : ∀ η > 0,
      Tendsto (fun n => P.real {ω | η ≤ dist (Y n ω) (π (D n ω))}) atTop (𝓝 0) := by
    intro η hη
    have h := (tendstoInMeasure_iff_norm.1 hYπ) η hη
    simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_dist] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [measureReal_def, Function.comp_def] using this
  have hsd : Tendsto (fun n => dist (s n) s₀) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hs
  have key : Tendsto μs atTop (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro F ⟨C, hC⟩ ⟨L, hL⟩
    have hFc : Continuous F := hL.continuous
    have hIB : ∀ n, ∫ x, F x ∂(μs n : Measure (S × M × 𝒞 × ℝ≥0)) =
        ∫ ω, F (D n ω, Y n ω, Q n ω, s n) ∂P := fun n =>
      integral_map (hB n).aemeasurable hFc.aestronglyMeasurable
    have hIμ : ∫ x, F x ∂(μ : Measure (S × M × 𝒞 × ℝ≥0)) =
        ∫ p, F (p.1, π p.1, p.2, s₀) ∂ν :=
      integral_map hΦm.aemeasurable hFc.aestronglyMeasurable
    show Tendsto (fun n => ∫ x, F x ∂(μs n : Measure (S × M × 𝒞 × ℝ≥0))) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure (S × M × 𝒞 × ℝ≥0))))
    rw [hIμ]
    refine Tendsto.congr (fun n => (hIB n).symm) ?_
    have hAF : Tendsto (fun n => ∫ ω, F (D n ω, π (D n ω), Q n ω, s₀) ∂P) atTop
        (𝓝 (∫ p, F (p.1, π p.1, p.2, s₀) ∂ν)) :=
      hlaw ((BoundedContinuousFunction.mkOfBound ⟨F, hFc⟩ C hC).compContinuous ⟨_, hΦc⟩)
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (4 * (L + 1)) with hη_def
    have hηpos : 0 < η := by positivity
    have hLη : (L : ℝ) * η ≤ ε / 4 := by
      rw [hη_def, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hdist := tendsto_iff_dist_tendsto_zero.1 hAF
    have hsum : Tendsto (fun n => (L : ℝ) * η + L * dist (s n) s₀ +
        C * P.real {ω | η ≤ dist (Y n ω) (π (D n ω))} +
        dist (∫ ω, F (D n ω, π (D n ω), Q n ω, s₀) ∂P) (∫ p, F (p.1, π p.1, p.2, s₀) ∂ν))
        atTop (𝓝 ((L : ℝ) * η + L * 0 + C * 0 + 0)) :=
      ((tendsto_const_nhds.add (hsd.const_mul _)).add ((hη η hηpos).const_mul C)).add hdist
    have hlt : (L : ℝ) * η + L * 0 + C * 0 + 0 < ε := by linarith
    filter_upwards [hsum.eventually_lt_const hlt] with n hn
    have hest : |∫ ω, F (D n ω, Y n ω, Q n ω, s n) ∂P -
        ∫ ω, F (D n ω, π (D n ω), Q n ω, s₀) ∂P| ≤
        L * η + L * dist (s n) s₀ + C * P.real {ω | η ≤ dist (Y n ω) (π (D n ω))} :=
      abs_integral_comp_sub_le_of_dist_le_add (P := P) (hB n) (hA n) hC hL
        (e := fun ω => dist (Y n ω) (π (D n ω))) dist_nonneg hηpos.le fun ω => by
          have h1 : 0 ≤ dist (Y n ω) (π (D n ω)) := dist_nonneg
          have h2 : 0 ≤ dist (s n) s₀ := dist_nonneg
          simp only [Prod.dist_eq, dist_self]
          exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))
    calc dist (∫ ω, F (D n ω, Y n ω, Q n ω, s n) ∂P) (∫ p, F (p.1, π p.1, p.2, s₀) ∂ν)
        ≤ dist (∫ ω, F (D n ω, Y n ω, Q n ω, s n) ∂P)
            (∫ ω, F (D n ω, π (D n ω), Q n ω, s₀) ∂P) +
          dist (∫ ω, F (D n ω, π (D n ω), Q n ω, s₀) ∂P)
            (∫ p, F (p.1, π p.1, p.2, s₀) ∂ν) := dist_triangle _ _ _
      _ < ε := by
        rw [Real.dist_eq (∫ ω, F (D n ω, Y n ω, Q n ω, s n) ∂P)]
        linarith
  have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 key) G
  change Tendsto (fun n => ∫ x, G x ∂(P.map fun ω => (D n ω, Y n ω, Q n ω, s n))) atTop
    (𝓝 (∫ x, G x ∂(ν.map fun p : S × 𝒞 => ((p.1, π p.1, p.2, s₀) : S × M × 𝒞 × ℝ≥0))))
    at hlim
  rw [integral_map hΦm.aemeasurable G.continuous.aestronglyMeasurable] at hlim
  exact hlim.congr fun n => integral_map (hB n).aemeasurable G.continuous.aestronglyMeasurable

/-- **Converging together with a projected coordinate**, almost everywhere measurable form. Let `S`,
`𝒞` be pseudo-metrizable second countable Borel spaces, `M` a pseudo-metric space whose open sets
are measurable, `π : S → M` continuous and measurable, and `D n`, `Y n`, `Q n` almost everywhere
measurable random elements of `S`, `M`, `𝒞`. If `(D n, Q n)` converges in law to `ν` on `S × 𝒞`,
`dist (Y n) (π (D n)) → 0` in probability and the deterministic times `s n` converge to `s₀`, then
for every bounded continuous `G : S × M × 𝒞 × ℝ≥0 → ℝ`,
`𝔼 G (D n, Y n, Q n, s n) → ∫ G (d, π d, q, s₀) dν(d, q)`. -/
theorem tendsto_integral_projection_of_tendstoInMeasure_dist_of_measurable {Ω S M 𝒞 : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    [PseudoMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
    [TopologicalSpace 𝒞] [TopologicalSpace.PseudoMetrizableSpace 𝒞] [SecondCountableTopology 𝒞]
    [MeasurableSpace 𝒞] [BorelSpace 𝒞]
    {D : ℕ → Ω → S} (hD : ∀ n, AEMeasurable (D n) P) {Y : ℕ → Ω → M}
    (hY : ∀ n, AEMeasurable (Y n) P) {Q : ℕ → Ω → 𝒞} (hQ : ∀ n, AEMeasurable (Q n) P)
    {s : ℕ → ℝ≥0} {s₀ : ℝ≥0} {π : S → M} (hπ : Continuous π) (hπm : Measurable π)
    {ν : Measure (S × 𝒞)}
    (hlaw : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω, Q n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hYπ : TendstoInMeasure P (fun n ω => dist (Y n ω) (π (D n ω))) atTop 0)
    (hs : Tendsto s atTop (𝓝 s₀)) :
    ∀ G : (S × M × 𝒞 × ℝ≥0) →ᵇ ℝ, Tendsto (fun n => ∫ ω, G (D n ω, Y n ω, Q n ω, s n) ∂P)
      atTop (𝓝 (∫ p, G (p.1, π p.1, p.2, s₀) ∂ν)) := by
  intro G
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric S
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric 𝒞
  have hlaw' : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f ((hD n).mk (D n) ω, (hQ n).mk (Q n) ω) ∂P) atTop
        (𝓝 (∫ p, f p ∂ν)) := by
    intro f
    refine (hlaw f).congr fun n => integral_congr_ae ?_
    filter_upwards [(hD n).ae_eq_mk, (hQ n).ae_eq_mk] with ω h1 h2
    rw [h1, h2]
  have hYπ' : TendstoInMeasure P
      (fun n ω => dist ((hY n).mk (Y n) ω) (π ((hD n).mk (D n) ω))) atTop 0 := by
    refine hYπ.congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
    filter_upwards [(hY n).ae_eq_mk, (hD n).ae_eq_mk] with ω h1 h2
    simp only [h1, h2]
  refine (tendsto_integral_projection_of_tendstoInMeasure_dist_of_pseudoMetricSpace
    (fun n => (hD n).measurable_mk) (fun n => (hY n).measurable_mk)
    (fun n => (hQ n).measurable_mk) hπ hπm hlaw' hYπ' hs G).congr fun n => integral_congr_ae ?_
  filter_upwards [(hD n).ae_eq_mk, (hY n).ae_eq_mk, (hQ n).ae_eq_mk] with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **Converging together with a projected coordinate.** Let `S`, `𝒞` be pseudo-metrizable second
countable Borel spaces, `M` a pseudo-metric space with its Borel `σ`-algebra, `π : S → M`
continuous, and `D n`, `Y n`, `Q n` almost everywhere measurable random elements of `S`, `M`, `𝒞`.
If `(D n, Q n)` converges in law to `ν` on `S × 𝒞`, `dist (Y n) (π (D n)) → 0` in probability and
the deterministic times `s n` converge to `s₀`, then for every bounded continuous
`G : S × M × 𝒞 × ℝ≥0 → ℝ`, `𝔼 G (D n, Y n, Q n, s n) → ∫ G (d, π d, q, s₀) dν(d, q)`. -/
theorem tendsto_integral_projection_of_tendstoInMeasure_dist {Ω S M 𝒞 : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace 𝒞] [TopologicalSpace.PseudoMetrizableSpace 𝒞] [SecondCountableTopology 𝒞]
    [MeasurableSpace 𝒞] [BorelSpace 𝒞]
    {D : ℕ → Ω → S} (hD : ∀ n, AEMeasurable (D n) P) {Y : ℕ → Ω → M}
    (hY : ∀ n, AEMeasurable (Y n) P) {Q : ℕ → Ω → 𝒞} (hQ : ∀ n, AEMeasurable (Q n) P)
    {s : ℕ → ℝ≥0} {s₀ : ℝ≥0} {π : S → M} (hπ : Continuous π) {ν : Measure (S × 𝒞)}
    (hlaw : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω, Q n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hYπ : TendstoInMeasure P (fun n ω => dist (Y n ω) (π (D n ω))) atTop 0)
    (hs : Tendsto s atTop (𝓝 s₀)) :
    ∀ G : (S × M × 𝒞 × ℝ≥0) →ᵇ ℝ, Tendsto (fun n => ∫ ω, G (D n ω, Y n ω, Q n ω, s n) ∂P)
      atTop (𝓝 (∫ p, G (p.1, π p.1, p.2, s₀) ∂ν)) :=
  tendsto_integral_projection_of_tendstoInMeasure_dist_of_measurable hD hY hQ hπ hπ.measurable
    hlaw hYπ hs

/-- **Converging together with a projected finite measure coordinate**, for the Lévy-Prokhorov
distance in the form Mathlib provides it: the finite measures on `ℂ` with the Lévy-Prokhorov
pseudo-metric form the type `LevyProkhorov (FiniteMeasure ℂ)`, whose distance is
`levyProkhorovDist`. If `(D n, Q n)` converges in law to `ν`, the random finite measures `μ n` satisfy
`levyProkhorovDist (μ n) (π (D n)) → 0` in probability and `s n → s₀`, then
`(D n, μ n, Q n, s n)` converges in law to the image of `ν` under `(d, q) ↦ (d, π d, q, s₀)`, the
measure coordinate carrying the Lévy-Prokhorov topology. -/
theorem tendsto_integral_levyProkhorov_projection_of_tendstoInMeasure_levyProkhorovDist
    {Ω S 𝒞 : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace 𝒞] [TopologicalSpace.PseudoMetrizableSpace 𝒞] [SecondCountableTopology 𝒞]
    [MeasurableSpace 𝒞] [BorelSpace 𝒞]
    [MeasurableSpace (LevyProkhorov (FiniteMeasure ℂ))]
    [BorelSpace (LevyProkhorov (FiniteMeasure ℂ))]
    {D : ℕ → Ω → S} (hD : ∀ n, AEMeasurable (D n) P) {μ : ℕ → Ω → FiniteMeasure ℂ}
    (hμ : ∀ n, AEMeasurable (fun ω => LevyProkhorov.ofMeasure (μ n ω)) P)
    {Q : ℕ → Ω → 𝒞} (hQ : ∀ n, AEMeasurable (Q n) P) {s : ℕ → ℝ≥0} {s₀ : ℝ≥0}
    {π : S → FiniteMeasure ℂ} (hπ : Continuous fun d => LevyProkhorov.ofMeasure (π d))
    {ν : Measure (S × 𝒞)}
    (hlaw : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D n ω, Q n ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hμπ : TendstoInMeasure P
      (fun n ω => levyProkhorovDist (μ n ω : Measure ℂ) (π (D n ω) : Measure ℂ)) atTop 0)
    (hs : Tendsto s atTop (𝓝 s₀)) :
    ∀ G : (S × LevyProkhorov (FiniteMeasure ℂ) × 𝒞 × ℝ≥0) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, G (D n ω, LevyProkhorov.ofMeasure (μ n ω), Q n ω, s n) ∂P) atTop
        (𝓝 (∫ p, G (p.1, LevyProkhorov.ofMeasure (π p.1), p.2, s₀) ∂ν)) :=
  tendsto_integral_projection_of_tendstoInMeasure_dist hD hμ hQ hπ hlaw hμπ hs

end LatticeProb
