import Mathlib
import LatticeProb.Topology.ContinuousMapBorel

/-!
# Convergence in law of an evaluated random law, up to an error tending to zero in probability

Let `X` be a random element of a pseudo-metrizable space `S` (the data) and `Q k` random elements of
a topological space `𝒞` such that `(X, Q k)` converges in law to a probability measure `ν` on
`S × 𝒞` (integrals of bounded continuous functions converge). If `G : 𝒞 → ℝ` is continuous and
`R k - G (Q k) → 0` in probability, then `(X, R k)` converges in law to the image of `ν` under
`(d, c) ↦ (d, G c)`: this is the continuous mapping theorem followed by converging together in the
second coordinate (Billingsley, *Convergence of probability measures*, Theorems 2.7 and 3.1).

The case of interest is `𝒞 = C(Z, Prob(E))` with the compact-open topology, a point `z : Z` and
`G c = ∫ F d(c z)` for a bounded continuous `F : E → ℝ`.

* `LatticeProb.abs_integral_prod_sub_le_of_lipschitzWith`: for a bounded Lipschitz `F` on `S × ℝ`,
  `|𝔼 F (X, R) - 𝔼 F (X, Y)| ≤ L η + M ℙ(η ≤ |R - Y|)`.
* `LatticeProb.tendsto_integral_prod_of_tendstoInMeasure_sub`: converging together in the second
  coordinate of `S × ℝ`, `S` pseudo-metric.
* `LatticeProb.continuous_integral_probabilityMeasure`: `μ ↦ ∫ F dμ` is continuous on `Prob(E)`.
* `LatticeProb.tendsto_integral_comp_of_tendsto_law_of_tendstoInMeasure_sub`: the statement for a
  continuous `G : 𝒞 → ℝ`.
* `LatticeProb.tendsto_integral_eval_of_tendsto_law_of_tendstoInMeasure_sub`: the statement for
  `𝒞 = C(Z, Prob(E))` and `G c = ∫ F d(c z)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

section PseudoMetric

variable {Ω S : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]

/-- A bounded Lipschitz function of `(X, R)` and of `(X, Y)` differs by at most `L η` where
`|R - Y| < η`, and by at most the bound `M` on the event `η ≤ |R - Y|`. -/
theorem abs_integral_prod_sub_le_of_lipschitzWith {X : Ω → S} (hX : Measurable X) {Y R : Ω → ℝ}
    (hY : Measurable Y) (hR : Measurable R) {F : S × ℝ → ℝ} {M : ℝ} {L : ℝ≥0}
    (hM : ∀ x y, dist (F x) (F y) ≤ M) (hF : LipschitzWith L F) {η : ℝ} (hη : 0 ≤ η) :
    |∫ ω, F (X ω, R ω) ∂P - ∫ ω, F (X ω, Y ω) ∂P| ≤ L * η + M * P.real {ω | η ≤ ‖R ω - Y ω‖} := by
  let Fb : (S × ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, hF.continuous⟩ M hM
  have hFm : Measurable F := hF.continuous.measurable
  have hIR : Integrable (fun ω => F (X ω, R ω)) P :=
    Integrable.of_bound (hFm.comp (hX.prodMk hR)).aestronglyMeasurable ‖Fb‖
      (ae_of_all _ fun ω => Fb.norm_coe_le_norm (X ω, R ω))
  have hIY : Integrable (fun ω => F (X ω, Y ω)) P :=
    Integrable.of_bound (hFm.comp (hX.prodMk hY)).aestronglyMeasurable ‖Fb‖
      (ae_of_all _ fun ω => Fb.norm_coe_le_norm (X ω, Y ω))
  have hS : MeasurableSet {ω | η ≤ ‖R ω - Y ω‖} :=
    measurableSet_le measurable_const (hR.sub hY).norm
  have hIrhs : Integrable (fun ω => (L : ℝ) * η +
      {ω | η ≤ ‖R ω - Y ω‖}.indicator (fun _ => M) ω) P :=
    (integrable_const _).add ((integrable_const M).indicator hS)
  rw [← integral_sub hIR hIY, ← Real.norm_eq_abs]
  calc ‖∫ ω, (F (X ω, R ω) - F (X ω, Y ω)) ∂P‖ ≤ ∫ ω, ‖F (X ω, R ω) - F (X ω, Y ω)‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((L : ℝ) * η + {ω | η ≤ ‖R ω - Y ω‖}.indicator (fun _ => M) ω) ∂P := by
        refine integral_mono (hIR.sub hIY).norm hIrhs fun ω => ?_
        by_cases h : η ≤ ‖R ω - Y ω‖
        · rw [Set.indicator_of_mem (show ω ∈ {ω | η ≤ ‖R ω - Y ω‖} from h)]
          have h3 := hM (X ω, R ω) (X ω, Y ω)
          rw [dist_eq_norm] at h3
          have hLη : (0 : ℝ) ≤ L * η := mul_nonneg L.2 hη
          linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | η ≤ ‖R ω - Y ω‖} from h), add_zero,
            ← dist_eq_norm]
          have h1 := hF.dist_le_mul (X ω, R ω) (X ω, Y ω)
          have h5 : dist (X ω, R ω) (X ω, Y ω) = ‖R ω - Y ω‖ := by
            simp only [Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg (R ω - Y ω))]
          rw [h5] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left (not_le.1 h).le L.2)
    _ = (L : ℝ) * η + M * P.real {ω | η ≤ ‖R ω - Y ω‖} := by
        rw [integral_add (integrable_const _) ((integrable_const M).indicator hS),
          integral_const, integral_indicator_const _ hS]
        simp [mul_comm]

/-- **Converging together in the second coordinate.** Let `X` be a random element of a
pseudo-metric space `S` and `Y k, R k` real random variables. If `(X, Y k)` converges in law to a
probability measure `ν` on `S × ℝ` and `R k - Y k → 0` in probability, then `(X, R k)` converges in
law to `ν`. -/
theorem tendsto_integral_prod_of_tendstoInMeasure_sub {X : Ω → S} (hX : Measurable X)
    {Y R : ℕ → Ω → ℝ} (hY : ∀ k, Measurable (Y k)) (hR : ∀ k, Measurable (R k))
    {ν : Measure (S × ℝ)} [IsProbabilityMeasure ν]
    (hXY : ∀ f : (S × ℝ) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (X ω, Y k ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hRY : TendstoInMeasure P (fun k ω => R k ω - Y k ω) atTop 0) (f : (S × ℝ) →ᵇ ℝ) :
    Tendsto (fun k => ∫ ω, f (X ω, R k ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)) := by
  have hXR : ∀ k, Measurable fun ω => (X ω, R k ω) := fun k => hX.prodMk (hR k)
  let μs : ℕ → ProbabilityMeasure (S × ℝ) := fun k =>
    ⟨P.map fun ω => (X ω, R k ω),
      (Measure.isProbabilityMeasure_map_iff (hXR k).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure (S × ℝ) := ⟨ν, inferInstance⟩
  have hRη : ∀ η > 0, Tendsto (fun k => P.real {ω | η ≤ ‖R k ω - Y k ω‖}) atTop (𝓝 0) := by
    intro η hη
    have h := (tendstoInMeasure_iff_norm.1 hRY) η hη
    simp only [Pi.zero_apply, sub_zero] at h
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [measureReal_def, Function.comp_def] using this
  have key : Tendsto μs atTop (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro F ⟨M, hM⟩ ⟨L, hL⟩
    have hFc : Continuous F := hL.continuous
    have hIntR : ∀ k, ∫ p, F p ∂(μs k : Measure (S × ℝ)) = ∫ ω, F (X ω, R k ω) ∂P := fun k =>
      integral_map (hXR k).aemeasurable hFc.aestronglyMeasurable
    show Tendsto (fun k => ∫ p, F p ∂(μs k : Measure (S × ℝ))) atTop (𝓝 (∫ p, F p ∂ν))
    refine Tendsto.congr (fun k => (hIntR k).symm) ?_
    have hYF : Tendsto (fun k => ∫ ω, F (X ω, Y k ω) ∂P) atTop (𝓝 (∫ p, F p ∂ν)) :=
      hXY (BoundedContinuousFunction.mkOfBound ⟨F, hFc⟩ M hM)
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (4 * (L + 1)) with hη_def
    have hηpos : 0 < η := by positivity
    have hLη : (L : ℝ) * η ≤ ε / 4 := by
      rw [hη_def, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hdist := tendsto_iff_dist_tendsto_zero.1 hYF
    have hB : Tendsto (fun k => (L : ℝ) * η + M * P.real {ω | η ≤ ‖R k ω - Y k ω‖} +
        dist (∫ ω, F (X ω, Y k ω) ∂P) (∫ p, F p ∂ν)) atTop (𝓝 ((L : ℝ) * η + M * 0 + 0)) :=
      (tendsto_const_nhds.add ((hRη η hηpos).const_mul M)).add hdist
    have hlt : (L : ℝ) * η + M * 0 + 0 < ε := by linarith
    filter_upwards [hB.eventually_lt_const hlt] with k hk
    have hest := abs_integral_prod_sub_le_of_lipschitzWith (P := P) hX (hY k) (hR k) hM hL
      hηpos.le
    calc dist (∫ ω, F (X ω, R k ω) ∂P) (∫ p, F p ∂ν)
        ≤ dist (∫ ω, F (X ω, R k ω) ∂P) (∫ ω, F (X ω, Y k ω) ∂P) +
          dist (∫ ω, F (X ω, Y k ω) ∂P) (∫ p, F p ∂ν) := dist_triangle _ _ _
      _ < ε := by
        simp only [Real.dist_eq] at hk ⊢
        linarith
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 key) f
  exact Tendsto.congr (fun k => integral_map (hXR k).aemeasurable
    f.continuous.aestronglyMeasurable) this

end PseudoMetric

/-- For a bounded continuous `F`, the integral `μ ↦ ∫ F dμ` is continuous for the topology of
convergence in distribution on the probability measures. -/
theorem continuous_integral_probabilityMeasure {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (F : E →ᵇ ℝ) :
    Continuous fun μ : ProbabilityMeasure E => ∫ x, F x ∂(μ : Measure E) :=
  continuous_iff_continuousAt.2 fun _ =>
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id F

/-- **Continuous mapping and converging together.** Let `X` be a random element of a
pseudo-metrizable space `S` and `Q k` random elements of `𝒞` such that `(X, Q k)` converges in law
to `ν` on `S × 𝒞`. If `G : 𝒞 → ℝ` is continuous and `R k - G (Q k) → 0` in probability, then
`(X, R k)` converges in law to the image of `ν` under `(d, c) ↦ (d, G c)`. -/
theorem tendsto_integral_comp_of_tendsto_law_of_tendstoInMeasure_sub {Ω S 𝒞 : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSpace S]
    [BorelSpace S] [TopologicalSpace 𝒞] [MeasurableSpace 𝒞] [OpensMeasurableSpace 𝒞]
    {X : Ω → S} (hX : AEMeasurable X P) {Q : ℕ → Ω → 𝒞} (hQ : ∀ k, AEMeasurable (Q k) P)
    {R : ℕ → Ω → ℝ} (hR : ∀ k, AEMeasurable (R k) P) {ν : Measure (S × 𝒞)}
    {G : 𝒞 → ℝ} (hG : Continuous G)
    (hlaw : ∀ f : (S × 𝒞) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (X ω, Q k ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hRG : TendstoInMeasure P (fun k ω => R k ω - G (Q k ω)) atTop 0) :
    ∀ f : (S × ℝ) →ᵇ ℝ, Tendsto (fun k => ∫ ω, f (X ω, R k ω) ∂P) atTop
      (𝓝 (∫ p, f (p.1, G p.2) ∂ν)) := by
  intro f
  have h1 : ν.real Set.univ = 1 := by
    have h := hlaw 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have : IsProbabilityMeasure ν :=
    ⟨by rw [measureReal_def] at h1; exact (ENNReal.toReal_eq_one_iff _).1 h1⟩
  have hGm : Measurable G := hG.measurable
  have hΦc : Continuous fun p : S × 𝒞 => (p.1, G p.2) :=
    continuous_fst.prodMk (hG.comp continuous_snd)
  have hΦm : Measurable fun p : S × 𝒞 => (p.1, G p.2) :=
    measurable_fst.prodMk (hGm.comp measurable_snd)
  have : IsProbabilityMeasure (ν.map fun p : S × 𝒞 => (p.1, G p.2)) :=
    (Measure.isProbabilityMeasure_map_iff hΦm.aemeasurable).2 inferInstance
  have hlaw' : ∀ g : (S × ℝ) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, g (hX.mk X ω, G ((hQ k).mk (Q k) ω)) ∂P) atTop
        (𝓝 (∫ p, g p ∂(ν.map fun p : S × 𝒞 => (p.1, G p.2)))) := by
    intro g
    have h := hlaw (g.compContinuous ⟨fun p : S × 𝒞 => (p.1, G p.2), hΦc⟩)
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at h
    rw [integral_map hΦm.aemeasurable g.continuous.aestronglyMeasurable]
    refine h.congr fun k => integral_congr_ae ?_
    filter_upwards [hX.ae_eq_mk, (hQ k).ae_eq_mk] with ω h1 h2
    rw [h1, h2]
  have hRG' : TendstoInMeasure P
      (fun k ω => (hR k).mk (R k) ω - G ((hQ k).mk (Q k) ω)) atTop 0 := by
    refine hRG.congr' (Eventually.of_forall fun k => ?_) EventuallyEq.rfl
    filter_upwards [(hR k).ae_eq_mk, (hQ k).ae_eq_mk] with ω h1 h2
    simp only [h1, h2]
  rw [← integral_map hΦm.aemeasurable f.continuous.aestronglyMeasurable]
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric S
  refine (tendsto_integral_prod_of_tendstoInMeasure_sub hX.measurable_mk
    (fun k => hGm.comp (hQ k).measurable_mk) (fun k => (hR k).measurable_mk) hlaw' hRG' f).congr
    fun k => integral_congr_ae ?_
  filter_upwards [hX.ae_eq_mk, (hR k).ae_eq_mk] with ω h1 h2
  rw [h1, h2]

/-- **Convergence in law of an evaluated random law.** Let `X` be a random element of a
pseudo-metrizable space `S`, `Q k` random continuous maps `Z → Prob(E)` (compact-open topology,
Borel `σ`-algebra) such that `(X, Q k)` converges in law to `ν` on `S × C(Z, Prob(E))`, `z : Z` and
`F : E → ℝ` bounded continuous. If `R k - ∫ F d(Q k z) → 0` in probability, then `(X, R k)`
converges in law to the image of `ν` under `(d, P) ↦ (d, ∫ F d(P z))`. -/
theorem tendsto_integral_eval_of_tendsto_law_of_tendstoInMeasure_sub {Ω S Z E : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [TopologicalSpace S] [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSpace S]
    [BorelSpace S] [TopologicalSpace Z] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    {X : Ω → S} (hX : AEMeasurable X P) {Q : ℕ → Ω → C(Z, ProbabilityMeasure E)}
    (hQ : ∀ k, AEMeasurable (Q k) P) {R : ℕ → Ω → ℝ} (hR : ∀ k, AEMeasurable (R k) P)
    {ν : Measure (S × C(Z, ProbabilityMeasure E))} (z : Z) (F : E →ᵇ ℝ)
    (hlaw : ∀ f : (S × C(Z, ProbabilityMeasure E)) →ᵇ ℝ,
      Tendsto (fun k => ∫ ω, f (X ω, Q k ω) ∂P) atTop (𝓝 (∫ p, f p ∂ν)))
    (hRF : TendstoInMeasure P (fun k ω => R k ω - ∫ x, F x ∂(Q k ω z : Measure E)) atTop 0) :
    ∀ f : (S × ℝ) →ᵇ ℝ, Tendsto (fun k => ∫ ω, f (X ω, R k ω) ∂P) atTop
      (𝓝 (∫ p, f (p.1, ∫ x, F x ∂(p.2 z : Measure E)) ∂ν)) :=
  tendsto_integral_comp_of_tendsto_law_of_tendstoInMeasure_sub hX hQ hR
    (G := fun c : C(Z, ProbabilityMeasure E) => ∫ x, F x ∂(c z : Measure E))
    ((continuous_integral_probabilityMeasure F).comp (continuous_eval_const z))
    hlaw hRF

end LatticeProb
