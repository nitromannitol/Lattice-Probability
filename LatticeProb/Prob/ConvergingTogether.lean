import Mathlib

/-!
# Converging together for a varying family of probability measures

If `X i` converges weakly to a measure `ν` (as `i` runs along a filter `l`, the law of `X i`
being `(P i).map (X i)`) and `Y i - X i` tends to `0` in probability, then `Y i` converges weakly
to `ν` as well (Billingsley, *Convergence of probability measures*, Theorem 3.1).  Mathlib proves
this for a single ambient probability measure; here the probability measure `P i` may depend on
the index.

* `LatticeProb.abs_integral_comp_sub_le_of_lipschitzWith`: for a bounded Lipschitz function `F`,
  `|𝔼 F (Y) - 𝔼 F (X)| ≤ L η + M ℙ(η ≤ ‖Y - X‖)`.
* `LatticeProb.tendsto_integral_comp_of_tendstoInMeasure_sub`: the converging-together lemma, for
  the test functions bounded and continuous, along a countably generated filter.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal NNReal

namespace LatticeProb

section Estimate

variable {Ω E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E]
  [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A bounded Lipschitz function of two random variables at distance `< η` differs by at most
`L η`, and by at most the bound `M` on the event `η ≤ ‖Y - X‖`. -/
theorem abs_integral_comp_sub_le_of_lipschitzWith {X Y : Ω → E} (hX : Measurable X)
    (hY : Measurable Y) {F : E → ℝ} {M : ℝ} {L : ℝ≥0} (hM : ∀ x y, dist (F x) (F y) ≤ M)
    (hF : LipschitzWith L F) {η : ℝ} (hη : 0 ≤ η) :
    |∫ ω, F (Y ω) ∂P - ∫ ω, F (X ω) ∂P| ≤ L * η + M * P.real {ω | η ≤ ‖Y ω - X ω‖} := by
  have hFm : Measurable F := hF.continuous.measurable
  have hM0 : 0 ≤ M := (dist_nonneg).trans (hM 0 0)
  have hbd : ∀ x, ‖F x‖ ≤ ‖F 0‖ + M := fun x => by
    have h1 := abs_sub_abs_le_abs_sub (F x) (F 0)
    have h2 := hM x 0
    rw [Real.dist_eq] at h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have hIY : Integrable (fun ω => F (Y ω)) P :=
    Integrable.of_bound (hFm.comp hY).aestronglyMeasurable (‖F 0‖ + M)
      (ae_of_all _ fun ω => hbd _)
  have hIX : Integrable (fun ω => F (X ω)) P :=
    Integrable.of_bound (hFm.comp hX).aestronglyMeasurable (‖F 0‖ + M)
      (ae_of_all _ fun ω => hbd _)
  have hS : MeasurableSet {ω | η ≤ ‖Y ω - X ω‖} :=
    measurableSet_le measurable_const (hY.sub hX).norm
  have hIrhs : Integrable (fun ω => (L : ℝ) * η +
      {ω | η ≤ ‖Y ω - X ω‖}.indicator (fun _ => M) ω) P :=
    (integrable_const _).add ((integrable_const M).indicator hS)
  rw [← integral_sub hIY hIX, ← Real.norm_eq_abs]
  calc ‖∫ ω, (F (Y ω) - F (X ω)) ∂P‖ ≤ ∫ ω, ‖F (Y ω) - F (X ω)‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((L : ℝ) * η + {ω | η ≤ ‖Y ω - X ω‖}.indicator (fun _ => M) ω) ∂P := by
        refine integral_mono (hIY.sub hIX).norm hIrhs fun ω => ?_
        by_cases h : η ≤ ‖Y ω - X ω‖
        · rw [Set.indicator_of_mem (show ω ∈ {ω | η ≤ ‖Y ω - X ω‖} from h)]
          have h3 := hM (Y ω) (X ω)
          rw [dist_eq_norm] at h3
          have hLη : (0 : ℝ) ≤ L * η := mul_nonneg L.2 hη
          linarith
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | η ≤ ‖Y ω - X ω‖} from h)]
          have h1 := hF.dist_le_mul (Y ω) (X ω)
          rw [dist_eq_norm, dist_eq_norm] at h1
          have h2 : ‖Y ω - X ω‖ ≤ η := (not_le.1 h).le
          have h4 := mul_le_mul_of_nonneg_left h2 L.2
          rw [add_zero]
          exact h1.trans h4
    _ = (L : ℝ) * η + M * P.real {ω | η ≤ ‖Y ω - X ω‖} := by
        rw [integral_add (integrable_const _) ((integrable_const M).indicator hS),
          integral_const, integral_indicator_const _ hS]
        simp [mul_comm]

end Estimate

/-- **Converging together.**  Let `X i, Y i : Ω → E` be measurable maps into a separable normed
group, `P i` probability measures on `Ω`, and `ν` a measure on `E` such that `X i` converges weakly
to `ν` along a countably generated filter `l` (integrals of bounded continuous functions
converge) and `Y i - X i → 0` in probability.  Then `Y i` converges weakly to `ν`. -/
theorem tendsto_integral_comp_of_tendstoInMeasure_sub {ι Ω E : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [NormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : ι → Measure Ω}
    [∀ i, IsProbabilityMeasure (P i)] {X Y : ι → Ω → E} (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) {ν : Measure E}
    (hXν : ∀ f : E →ᵇ ℝ, Tendsto (fun i => ∫ ω, f (X i ω) ∂P i) l (𝓝 (∫ x, f x ∂ν)))
    (hXY : ∀ η > 0, Tendsto (fun i => P i {ω | η ≤ ‖Y i ω - X i ω‖}) l (𝓝 0))
    (f : E →ᵇ ℝ) : Tendsto (fun i => ∫ ω, f (Y i ω) ∂P i) l (𝓝 (∫ x, f x ∂ν)) := by
  rcases eq_or_neBot l with h | hne
  · subst h
    exact tendsto_bot
  have h1 : ν.real Set.univ = 1 := by
    have h := hXν 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hν : IsProbabilityMeasure ν :=
    ⟨by rw [measureReal_def] at h1; exact (ENNReal.toReal_eq_one_iff _).1 h1⟩
  let μs : ι → ProbabilityMeasure E := fun i =>
    ⟨(P i).map (Y i), (Measure.isProbabilityMeasure_map_iff (hY i).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure E := ⟨ν, hν⟩
  have key : Tendsto μs l (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro F ⟨M, hM⟩ ⟨L, hL⟩
    have hFc : Continuous F := hL.continuous
    have hIntY : ∀ i, ∫ ω, F ω ∂(μs i : Measure E) = ∫ ω, F (Y i ω) ∂P i := fun i =>
      integral_map (hY i).aemeasurable hFc.aestronglyMeasurable
    show Tendsto (fun i => ∫ ω, F ω ∂(μs i : Measure E)) l (𝓝 (∫ ω, F ω ∂ν))
    refine Tendsto.congr (fun i => (hIntY i).symm) ?_
    have hXF : Tendsto (fun i => ∫ ω, F (X i ω) ∂P i) l (𝓝 (∫ x, F x ∂ν)) :=
      hXν (BoundedContinuousFunction.mkOfBound ⟨F, hFc⟩ M hM)
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (4 * (L + 1)) with hη_def
    have hηpos : 0 < η := by positivity
    have hLη : (L : ℝ) * η ≤ ε / 4 := by
      rw [hη_def, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hp : Tendsto (fun i => (P i).real {ω | η ≤ ‖Y i ω - X i ω‖}) l (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hXY η hηpos)
      simpa [measureReal_def, Function.comp_def] using this
    have hdist := tendsto_iff_dist_tendsto_zero.1 hXF
    have hB : Tendsto (fun i => (L : ℝ) * η + M * (P i).real {ω | η ≤ ‖Y i ω - X i ω‖} +
        dist (∫ ω, F (X i ω) ∂P i) (∫ x, F x ∂ν)) l (𝓝 ((L : ℝ) * η + M * 0 + 0)) :=
      (tendsto_const_nhds.add (hp.const_mul M)).add hdist
    have hlt : (L : ℝ) * η + M * 0 + 0 < ε := by linarith
    filter_upwards [hB.eventually_lt_const hlt] with i hi
    have hest := abs_integral_comp_sub_le_of_lipschitzWith (P := P i) (hX i) (hY i) hM hL
      (η := η) hηpos.le
    calc dist (∫ ω, F (Y i ω) ∂P i) (∫ ω, F ω ∂ν)
        ≤ dist (∫ ω, F (Y i ω) ∂P i) (∫ ω, F (X i ω) ∂P i) +
          dist (∫ ω, F (X i ω) ∂P i) (∫ x, F x ∂ν) := dist_triangle _ _ _
      _ < ε := by
        simp only [Real.dist_eq] at hi ⊢
        linarith
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 key) f
  exact Tendsto.congr (fun i => integral_map (hY i).aemeasurable
    f.continuous.aestronglyMeasurable) this

end LatticeProb
